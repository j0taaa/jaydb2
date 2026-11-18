//! Live engine store: versioned, indexed host-owned state. See docs/live-engine.md.
#![allow(dead_code)] // Integrated with the host in a separate change.

mod ops;
mod schema;
mod transaction;
mod value;

pub use ops::{Answer, Collection, Operation, User};
#[allow(unused_imports)] // Public constructors for the host integration.
pub use schema::{Column, ColumnKind, Schema, TableSchema};
pub use transaction::Transaction;
pub use value::{CodecError, Fields, Value, decode, encode};

use imbl::OrdMap;
use std::{collections::BTreeMap, error::Error, fmt, sync::Arc};
use value::{HEADER, text_size, write_list_header, write_record_header, write_text, write_value};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StoreError {
    Data,
    Limit,
    Conflict,
    InvalidLsn,
}

impl fmt::Display for StoreError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Data => "data",
            Self::Limit => "limit",
            Self::Conflict => "transaction conflict",
            Self::InvalidLsn => "LSN must increase",
        })
    }
}

impl Error for StoreError {}

impl From<CodecError> for StoreError {
    fn from(_: CodecError) -> Self {
        Self::Data
    }
}

/// Collection, key, and canonical row record bytes (None for removal).
pub type Write = (Collection, String, Option<Vec<u8>>);

type Rows = OrdMap<String, Arc<Row>>;
type RowWrites = BTreeMap<String, Option<Arc<Row>>>;
type Changes = BTreeMap<Collection, RowWrites>;

struct Row {
    value: Value,
    size: usize,
}

impl Row {
    // The schema checks field names, order and scalar types before construction.
    fn new(fields: Fields) -> Arc<Self> {
        let size = HEADER
            + fields
                .iter()
                .map(|(name, value)| {
                    text_size(name)
                        + match value {
                            Value::Absent | Value::Bool(_) => 1,
                            Value::Int(_) => HEADER,
                            Value::Text(text) => text_size(text),
                            _ => unreachable!("row fields are scalars"),
                        }
                })
                .sum::<usize>();
        Arc::new(Self {
            value: Value::Record(fields),
            size,
        })
    }

    fn fields(&self) -> &Fields {
        let Value::Record(fields) = &self.value else {
            unreachable!()
        };
        fields
    }

    fn text(&self, index: usize) -> &str {
        let Value::Text(text) = &self.fields()[index].1 else {
            unreachable!()
        };
        text
    }

    fn credential(&self) -> &str {
        self.text(0)
    }

    fn user(&self, key: &str) -> User {
        User {
            id: key.to_owned(),
            kind: self.text(2).to_owned(),
            credential: self.credential().to_owned(),
        }
    }
}

#[derive(Clone, Default)]
struct CollectionState {
    rows: Rows,
    last_write: OrdMap<String, u64>,
    membership_lsn: u64,
}

/// An immutable published version. Cloning only shares the persistent roots.
#[derive(Clone)]
pub struct Snapshot {
    schema: Arc<Schema>,
    lsn: u64,
    size: usize,
    collections: OrdMap<Collection, CollectionState>,
    credentials: OrdMap<String, String>,
    credential_lsn: OrdMap<String, u64>,
}

impl Snapshot {
    fn blank(schema: Schema, lsn: u64) -> Self {
        let mut collections = OrdMap::new();
        collections.insert(None, CollectionState::default());
        for table in schema.tables() {
            collections.insert(Some(table.name.clone()), CollectionState::default());
        }
        // State record, tables list and users list; each table contains
        // a record with a name value and an empty rows list.
        let size = HEADER * 3
            + text_size("tables")
            + text_size("users")
            + schema
                .tables()
                .iter()
                .map(|table| {
                    HEADER * 2 + text_size("name") + text_size(&table.name) + text_size("rows")
                })
                .sum::<usize>();
        Self {
            schema: Arc::new(schema),
            lsn,
            size,
            collections,
            credentials: OrdMap::new(),
            credential_lsn: OrdMap::new(),
        }
    }

    pub fn empty(schema: Schema, lsn: u64) -> Result<Self, StoreError> {
        let state = Self::blank(schema, lsn);
        state.check_limit()?;
        Ok(state)
    }

    /// Open the exact root encoding of D.state_value at a checkpoint LSN.
    pub fn load(schema: Schema, lsn: u64, bytes: &[u8]) -> Result<Self, StoreError> {
        let fields: [(String, Value); 2] = decode(bytes)?
            .into_fields()?
            .try_into()
            .map_err(|_| StoreError::Data)?;
        let [(tables_name, tables), (users_name, users)] = fields;
        let tables = tables.into_list()?;
        if tables_name != "tables" || users_name != "users" || tables.len() != schema.tables().len()
        {
            return Err(StoreError::Data);
        }
        let mut state = Self::blank(schema, lsn);
        for (table, schema) in tables.into_iter().zip(state.schema.tables()) {
            let fields: [(String, Value); 2] = table
                .into_fields()?
                .try_into()
                .map_err(|_| StoreError::Data)?;
            let [(name_field, name), (rows_field, rows)] = fields;
            if name_field != "name" || name.into_text()? != schema.name || rows_field != "rows" {
                return Err(StoreError::Data);
            }
            let collection = state
                .collections
                .get_mut(&Some(schema.name.clone()))
                .unwrap();
            collection.rows = load_rows(rows, schema)?;
        }
        let users = load_rows(users, state.schema.table(&None).unwrap())?;
        for (key, row) in &users {
            if row.credential().is_empty()
                || state
                    .credentials
                    .insert(row.credential().to_owned(), key.clone())
                    .is_some()
            {
                return Err(StoreError::Data);
            }
        }
        state.collections.get_mut(&None).unwrap().rows = users;
        state.size = bytes.len();
        state.check_limit()?;
        Ok(state)
    }

    pub fn save(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(self.size);
        write_record_header(&mut out, 2);
        write_text(&mut out, "tables");
        write_list_header(&mut out, self.schema.tables().len());
        for (name, table) in &self.collections {
            if let Some(name) = name {
                write_record_header(&mut out, 2);
                write_text(&mut out, "name");
                write_text(&mut out, name);
                write_text(&mut out, "rows");
                write_rows(&mut out, &table.rows);
            }
        }
        write_text(&mut out, "users");
        write_rows(&mut out, &self.collections[&None].rows);
        debug_assert_eq!(out.len(), self.size);
        out
    }

    pub fn lsn(&self) -> u64 {
        self.lsn
    }

    pub fn canonical_size(&self) -> u64 {
        self.size as u64
    }

    pub fn authenticate(&self, credential: &str) -> Option<User> {
        let key = self.credentials.get(credential)?;
        Some(self.collections[&None].rows[key].user(key))
    }

    pub fn begin(&self) -> Transaction {
        Transaction::new(self.clone())
    }

    /// Apply a logged write set at a strictly later LSN.
    pub fn apply_write_set(&self, lsn: u64, writes: &[Write]) -> Result<Self, StoreError> {
        self.check_lsn(lsn)?;
        let mut changes = Changes::new();
        for (collection, key, bytes) in writes {
            let schema = self.schema.table(collection).ok_or(StoreError::Data)?;
            let row = if let Some(bytes) = bytes {
                let fields = decode(bytes)?.into_fields()?;
                if !schema.valid_row(key, &fields) {
                    return Err(StoreError::Data);
                }
                Some(Row::new(fields))
            } else {
                None
            };
            if changes
                .entry(collection.clone())
                .or_default()
                .insert(key.clone(), row)
                .is_some()
            {
                return Err(StoreError::Data);
            }
        }
        self.apply(lsn, &changes)
    }

    fn check_lsn(&self, lsn: u64) -> Result<(), StoreError> {
        if lsn > self.lsn {
            Ok(())
        } else {
            Err(StoreError::InvalidLsn)
        }
    }

    fn check_limit(&self) -> Result<(), StoreError> {
        if self.canonical_size() <= self.schema.state_limit() {
            Ok(())
        } else {
            Err(StoreError::Limit)
        }
    }

    // Rows have already passed their schema checks. Drop old credential
    // entries before assigning new ones so a credential can move between users.
    fn apply(&self, lsn: u64, changes: &Changes) -> Result<Self, StoreError> {
        let mut next = self.clone();
        let mut additions = Vec::new();
        for (collection, writes) in changes {
            let table = next.collections.get_mut(collection).unwrap();
            for (key, row) in writes {
                let old = table.rows.get(key);
                if collection.is_none() {
                    let before = old.map(|row| row.credential());
                    let after = row.as_ref().map(|row| row.credential());
                    if before != after {
                        if let Some(credential) = before {
                            next.credentials.remove(credential);
                            next.credential_lsn.insert(credential.to_owned(), lsn);
                        }
                        if let Some(credential) = after {
                            additions.push((credential, key));
                        }
                    }
                }
                if old.is_some() != row.is_some() {
                    table.membership_lsn = lsn;
                }
                next.size -= old.map_or(0, |row| row.size);
                match row {
                    Some(row) => {
                        table.rows.insert(key.clone(), Arc::clone(row));
                        next.size += row.size;
                    }
                    None => {
                        table.rows.remove(key);
                    }
                }
                table.last_write.insert(key.clone(), lsn);
            }
        }
        for (credential, key) in additions {
            if credential.is_empty()
                || next
                    .credentials
                    .insert(credential.to_owned(), key.clone())
                    .is_some()
            {
                return Err(StoreError::Data);
            }
            next.credential_lsn.insert(credential.to_owned(), lsn);
        }
        next.check_limit()?;
        next.lsn = lsn;
        Ok(next)
    }
}

fn load_rows(value: Value, schema: &TableSchema) -> Result<Rows, StoreError> {
    let key_index = schema.column_index(&schema.key).unwrap();
    let mut rows = Rows::new();
    for value in value.into_list()? {
        let fields = value.into_fields()?;
        let Some((_, Value::Text(key))) = fields.get(key_index) else {
            return Err(StoreError::Data);
        };
        // UTF-8 byte order equals the scalar order used by Bend's String.is_lt.
        if rows.get_max().is_some_and(|(previous, _)| previous >= key)
            || !schema.valid_row(key, &fields)
        {
            return Err(StoreError::Data);
        }
        rows.insert(key.clone(), Row::new(fields));
    }
    Ok(rows)
}

fn write_rows(out: &mut Vec<u8>, rows: &Rows) {
    write_list_header(out, rows.len());
    for row in rows.values() {
        write_value(out, &row.value).expect("stored rows are canonical");
    }
}

#[cfg(test)]
mod tests;
