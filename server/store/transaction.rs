use super::{
    Answer, Collection, Operation, Row, RowWrites, Rows, Snapshot, StoreError, User, Write, encode,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

struct Overlay {
    // A shared root with only this transaction's changed paths copied.
    rows: Rows,
    writes: RowWrites,
}

pub struct Transaction {
    base: Snapshot,
    overlay: BTreeMap<Collection, Overlay>,
    row_reads: BTreeSet<(Collection, String)>,
    membership_reads: BTreeSet<Collection>,
    credential_reads: BTreeSet<String>,
}

impl Transaction {
    pub(super) fn new(base: Snapshot) -> Self {
        Self {
            base,
            overlay: BTreeMap::new(),
            row_reads: BTreeSet::new(),
            membership_reads: BTreeSet::new(),
            credential_reads: BTreeSet::new(),
        }
    }

    pub fn snapshot_lsn(&self) -> u64 {
        self.base.lsn
    }

    pub(super) fn rows(&self, collection: &Collection) -> &Rows {
        self.overlay.get(collection).map_or_else(
            || &self.base.collections[collection].rows,
            |overlay| &overlay.rows,
        )
    }

    fn write(&mut self, collection: Collection, key: String, row: Option<Arc<Row>>) {
        let overlay = self
            .overlay
            .entry(collection.clone())
            .or_insert_with(|| Overlay {
                rows: self.base.collections[&collection].rows.clone(),
                writes: RowWrites::new(),
            });
        match &row {
            Some(row) => {
                overlay.rows.insert(key.clone(), Arc::clone(row));
            }
            None => {
                overlay.rows.remove(&key);
            }
        }
        overlay.writes.insert(key, row);
    }

    /// Query the credential index plus pending user writes. If the working
    /// registry temporarily has duplicate credentials, Bend picks the first ID.
    pub fn authenticate(&mut self, credential: &str) -> Option<User> {
        self.credential_reads.insert(credential.to_owned());
        let rows = self.rows(&None);
        let indexed_key = self.base.credentials.get(credential).filter(|key| {
            rows.get(*key)
                .is_some_and(|row| row.credential() == credential)
        });
        let overlay_key = self.overlay.get(&None).and_then(|overlay| {
            overlay.writes.iter().find_map(|(key, row)| {
                row.as_ref()
                    .filter(|row| row.credential() == credential)
                    .map(|_| key)
            })
        });
        let key = indexed_key.into_iter().chain(overlay_key).min()?;
        let user = rows[key].user(key);
        // Authentication also returns the user kind, which can change while
        // the credential still points to the same ID.
        self.row_reads.insert((None, user.id.clone()));
        Some(user)
    }

    pub fn operate(&mut self, operation: Operation) -> Answer {
        if let Operation::Authenticate { credential } = operation {
            return self
                .authenticate(&credential)
                .map_or(Answer::NoUser, Answer::User);
        }
        let Some(schema) = self.base.schema.table(operation.collection()) else {
            return Answer::FailureData;
        };
        // Every Rust String already passes D.address_op_valid's Unicode check.
        match operation {
            Operation::ReadCell {
                collection,
                key,
                column,
            } => {
                let Some(index) = schema.column_index(&column) else {
                    return Answer::FailureData;
                };
                let answer = self
                    .rows(&collection)
                    .get(&key)
                    .map_or(Answer::RowAbsent, |row| {
                        Answer::Cell(row.fields()[index].1.clone())
                    });
                self.row_reads.insert((collection, key));
                answer
            }
            Operation::Existence { collection, key } => {
                let exists = self.rows(&collection).contains_key(&key);
                self.row_reads.insert((collection, key));
                Answer::Existence(exists)
            }
            Operation::Count { collection } => {
                let count = self.rows(&collection).len();
                self.membership_reads.insert(collection);
                Answer::Count(count)
            }
            Operation::Keys { collection } => {
                let keys = self.rows(&collection).keys().cloned().collect();
                self.membership_reads.insert(collection);
                Answer::Keys(keys)
            }
            Operation::DefineRow {
                collection,
                key,
                fields,
            } => {
                if !schema.valid_row(&key, &fields) {
                    return Answer::FailureData;
                }
                self.write(collection, key, Some(Row::new(fields)));
                Answer::Changed
            }
            Operation::DefineColumn {
                collection,
                key,
                column,
                value,
            } => {
                let Some(index) = schema.column_index(&column) else {
                    return Answer::FailureData;
                };
                if !schema.valid_column_write(index, &key, &value) {
                    return Answer::FailureData;
                }
                if let Some(row) = self.rows(&collection).get(&key) {
                    let mut fields = row.fields().clone();
                    fields[index].1 = value;
                    self.write(collection, key, Some(Row::new(fields)));
                } else {
                    // A concurrent insert would turn this no-op into a write.
                    self.row_reads.insert((collection, key));
                }
                Answer::Changed
            }
            Operation::RemoveRow { collection, key } => {
                self.write(collection, key, None);
                Answer::Changed
            }
            Operation::Authenticate { .. } => unreachable!(),
        }
    }

    /// Revalidate the read and write dependencies against the latest snapshot
    /// in the same publication history. Also usable when no writes will publish.
    pub fn validate(&self, current: &Snapshot) -> Result<(), StoreError> {
        if !Arc::ptr_eq(&self.base.schema, &current.schema) || current.lsn < self.base.lsn {
            return Err(StoreError::Conflict);
        }
        let start = self.base.lsn;
        let row_changed = |collection: &Collection, key: &String| {
            current.collections[collection]
                .last_write
                .get(key)
                .is_some_and(|lsn| *lsn > start)
        };
        if self
            .row_reads
            .iter()
            .any(|(collection, key)| row_changed(collection, key))
            || self.overlay.iter().any(|(collection, overlay)| {
                overlay
                    .writes
                    .keys()
                    .any(|key| row_changed(collection, key))
            })
            || self
                .membership_reads
                .iter()
                .any(|collection| current.collections[collection].membership_lsn > start)
            || self.credential_reads.iter().any(|credential| {
                current
                    .credential_lsn
                    .get(credential)
                    .is_some_and(|lsn| *lsn > start)
            })
        {
            return Err(StoreError::Conflict);
        }
        Ok(())
    }

    /// Return final row changes for the WAL. Only publish them after commit succeeds.
    pub fn write_set(&self) -> Vec<Write> {
        self.overlay
            .iter()
            .flat_map(|(collection, overlay)| {
                overlay.writes.iter().map(|(key, row)| {
                    let bytes = row
                        .as_ref()
                        .map(|row| encode(&row.value).expect("stored rows are canonical"));
                    (collection.clone(), key.clone(), bytes)
                })
            })
            .collect()
    }

    /// Stage a candidate on the latest snapshot after OCC, structure and size
    /// checks. The caller controls durability and publication of the candidate.
    pub fn commit(self, current: &Snapshot, lsn: u64) -> Result<Snapshot, StoreError> {
        self.validate(current)?;
        current.check_lsn(lsn)?;
        let changes = self
            .overlay
            .into_iter()
            .map(|(collection, overlay)| (collection, overlay.writes))
            .collect();
        current.apply(lsn, &changes)
    }
}
