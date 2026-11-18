//! The committer is the sole writer of the published snapshot and WAL.
use crate::storage::{self, Durable};
use crate::store::{Snapshot, StoreError, Transaction};
use crate::wal::{Record, WriteEntry};
use crate::{Error, Result, error_frame};
use std::collections::BTreeMap;
use std::ops::Deref;
use std::sync::{Arc, Mutex, mpsc};
use std::thread::{self, JoinHandle};

const PRUNE_INTERVAL: u64 = 256;

struct Published {
    snapshot: Snapshot,
    running: BTreeMap<u64, usize>,
}

pub struct ReadSnapshot<'a> {
    published: &'a Mutex<Published>,
    snapshot: Snapshot,
}

impl Deref for ReadSnapshot<'_> {
    type Target = Snapshot;

    fn deref(&self) -> &Snapshot {
        &self.snapshot
    }
}

impl Drop for ReadSnapshot<'_> {
    fn drop(&mut self) {
        let mut state = self.published.lock().unwrap();
        let lsn = self.snapshot.lsn();
        let count = state.running.get_mut(&lsn).unwrap();
        *count -= 1;
        if *count == 0 {
            state.running.remove(&lsn);
        }
    }
}

pub struct Completed {
    pub response: Vec<u8>,
    pub snapshot: Snapshot,
    pub wal_batch: usize,
}

impl Completed {
    pub fn new(response: Vec<u8>, snapshot: &Snapshot) -> Self {
        Self {
            response,
            snapshot: snapshot.clone(),
            wal_batch: 0,
        }
    }
}

struct Submission {
    transaction: Transaction,
    response: Vec<u8>,
    publish: bool,
    reply: mpsc::Sender<Result<Option<Completed>>>,
}

enum Command {
    Submit(Submission),
    Epoch {
        snapshot: Snapshot,
        descriptor: Vec<u8>,
        state: Vec<u8>,
        reply: mpsc::Sender<Result<()>>,
    },
}

pub struct Committer {
    published: Arc<Mutex<Published>>,
    sender: Option<mpsc::Sender<Command>>,
    thread: Option<JoinHandle<()>>,
}

impl Committer {
    pub fn start(mut snapshot: Snapshot, storage: Option<Durable>) -> Result<Self> {
        snapshot.prune_versions(snapshot.lsn());
        let published = Arc::new(Mutex::new(Published {
            snapshot,
            running: BTreeMap::new(),
        }));
        let (sender, pending) = mpsc::channel();
        let state = Arc::clone(&published);
        let thread = thread::Builder::new()
            .name("jaydb-commit".into())
            .spawn(move || run(&state, storage, pending))?;
        Ok(Self {
            published,
            sender: Some(sender),
            thread: Some(thread),
        })
    }

    pub fn read(&self) -> ReadSnapshot<'_> {
        let mut state = self.published.lock().unwrap();
        let snapshot = state.snapshot.clone();
        *state.running.entry(snapshot.lsn()).or_default() += 1;
        ReadSnapshot {
            published: &self.published,
            snapshot,
        }
    }

    // The caller keeps its snapshot pinned until the reply, including while
    // the transaction is queued. None means it must execute again.
    pub fn submit(
        &self,
        base: &ReadSnapshot<'_>,
        transaction: Transaction,
        response: Vec<u8>,
        publish: bool,
    ) -> Result<Option<Completed>> {
        debug_assert_eq!(base.lsn(), transaction.snapshot_lsn());
        if !transaction.has_writes() {
            return Ok(Some(Completed::new(response, base)));
        }
        let (reply, received) = mpsc::channel();
        self.sender
            .as_ref()
            .unwrap()
            .send(Command::Submit(Submission {
                transaction,
                response,
                publish,
                reply,
            }))
            .map_err(|_| committer_stopped())?;
        received.recv().map_err(|_| committer_stopped())?
    }

    // Exclusive admission holds through this reply. All earlier submissions
    // have finished, and no transaction can pin either snapshot during the switch.
    pub fn publish_epoch(
        &self,
        snapshot: Snapshot,
        descriptor: Vec<u8>,
        state: Vec<u8>,
    ) -> Result<()> {
        let (reply, received) = mpsc::channel();
        self.sender
            .as_ref()
            .unwrap()
            .send(Command::Epoch {
                snapshot,
                descriptor,
                state,
                reply,
            })
            .map_err(|_| committer_stopped())?;
        received.recv().map_err(|_| committer_stopped())?
    }
}

impl Drop for Committer {
    fn drop(&mut self) {
        drop(self.sender.take());
        if let Some(thread) = self.thread.take() {
            let _ = thread.join();
        }
    }
}

fn committer_stopped() -> Error {
    storage::uncertain("committer stopped")
}

fn run(
    published: &Mutex<Published>,
    mut storage: Option<Durable>,
    pending: mpsc::Receiver<Command>,
) {
    let mut pruned_through = published.lock().unwrap().snapshot.lsn();
    let mut next = None;
    while let Some(command) = next.take().or_else(|| pending.recv().ok()) {
        let first = match command {
            Command::Submit(first) => first,
            Command::Epoch {
                snapshot,
                descriptor,
                state,
                reply,
            } => {
                let previous = published.lock().unwrap().snapshot.lsn();
                if previous.checked_add(1) != Some(snapshot.lsn()) {
                    let _ = reply.send(Err(Error::new("HOST_STORE", "invalid epoch sequence")));
                    return;
                }
                if let Some(storage) = &mut storage
                    && let Err(error) = storage
                        .append_epoch(snapshot.lsn(), descriptor, state)
                        .and_then(|()| storage.checkpoint(previous, &snapshot))
                {
                    storage::fail_stop(format_args!("{}", error.message));
                }
                pruned_through = snapshot.lsn();
                published.lock().unwrap().snapshot = snapshot;
                let _ = reply.send(Ok(()));
                continue;
            }
        };
        let mut batch = vec![first];
        while let Ok(command) = pending.try_recv() {
            match command {
                Command::Submit(submission) => batch.push(submission),
                command => {
                    next = Some(command);
                    break;
                }
            }
        }
        let mut current = published.lock().unwrap().snapshot.clone();
        let previous_lsn = current.lsn();
        let mut records = Vec::new();
        let mut replies = Vec::new();
        for Submission {
            transaction,
            response,
            publish,
            reply,
        } in batch
        {
            let Some(lsn) = current.lsn().checked_add(1) else {
                let _ = reply.send(Err(Error::new(
                    "HOST_STORE",
                    "publication sequence exhausted",
                )));
                return;
            };
            let writes = (publish && storage.is_some()).then(|| transaction.write_set());
            let mut logged = false;
            let outcome = match transaction.commit(&current, lsn) {
                Ok(next) if publish => {
                    if let Some(writes) = writes {
                        records.push(Record::Commit {
                            lsn,
                            writes: writes
                                .into_iter()
                                .map(|(collection, key, row)| WriteEntry {
                                    collection,
                                    key,
                                    row,
                                })
                                .collect(),
                        });
                        logged = true;
                    }
                    current = next;
                    Some(Completed::new(response, &current))
                }
                Ok(_) => Some(Completed::new(response, &current)),
                Err(StoreError::Conflict) => None,
                Err(StoreError::Data) => Some(Completed::new(error_frame("data"), &current)),
                Err(StoreError::Limit) => Some(Completed::new(error_frame("limit"), &current)),
                Err(error) => {
                    let _ = reply.send(Err(Error::new("HOST_STORE", error.to_string())));
                    return;
                }
            };
            replies.push((reply, outcome, logged));
        }
        let batch_size = records.len();
        let durable = if let Some(storage) = storage.as_ref().filter(|_| !records.is_empty()) {
            storage
                .append(&records)
                .and_then(|()| storage.checkpoint(previous_lsn, &current))
        } else {
            Ok(())
        };
        if let Err(error) = durable {
            storage::fail_stop(format_args!("{}", error.message));
        }
        if current.lsn() != previous_lsn {
            if previous_lsn / PRUNE_INTERVAL != current.lsn() / PRUNE_INTERVAL {
                // Until publication, any newly opened snapshot sees previous_lsn.
                let oldest = published
                    .lock()
                    .unwrap()
                    .running
                    .first_key_value()
                    .map_or(previous_lsn, |(&lsn, _)| lsn);
                if oldest > pruned_through {
                    current.prune_versions(oldest);
                    pruned_through = oldest;
                }
            }
            published.lock().unwrap().snapshot = current;
        }
        for (reply, mut outcome, logged) in replies {
            if logged {
                outcome.as_mut().unwrap().wal_batch = batch_size;
            }
            let _ = reply.send(Ok(outcome));
        }
    }
}
