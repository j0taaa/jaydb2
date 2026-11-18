use crate::store::{Schema, Snapshot};
use crate::wal::{Log, Record};
use crate::{Error, Limits, Result, diagnostic};
use std::path::Path;
use std::sync::{Arc, mpsc};
use std::thread::{self, JoinHandle};

use std::io;
#[cfg(feature = "storage-fault-injection")]
use std::io::{Read, Write};

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    Create,
    Open,
}

// Not compiled into production. Tests arm the hook only after initialization.
// A Unix socket supplies a deterministic boundary without timing races.
pub fn fault_point(point: &str) -> io::Result<()> {
    #[cfg(feature = "storage-fault-injection")]
    if std::env::var("JAYDB_STORAGE_FAULT").as_deref() == Ok(point) {
        if let Ok(socket) = std::env::var("JAYDB_STORAGE_BARRIER") {
            let mut stream = std::os::unix::net::UnixStream::connect(socket)?;
            stream.write_all(point.as_bytes())?;
            stream.read_exact(&mut [0])?;
        }
        return Err(io::Error::from_raw_os_error(5)); // EIO
    }
    let _ = point;
    Ok(())
}

const CHECKPOINT_INTERVAL: u64 = 256;

pub struct Durable {
    log: Arc<Log>,
    checkpoints: Option<mpsc::SyncSender<Snapshot>>,
    checkpoint_thread: Option<JoinHandle<()>>,
}

impl Durable {
    pub fn start(
        path: &Path,
        mode: Mode,
        mut descriptor: Vec<u8>,
        limits: &Limits,
        schema: Schema,
        initial: &[u8],
    ) -> Result<(Self, Snapshot)> {
        // Bind the exact frozen environment (including the controller) and
        // the three evaluated limits, with fixed-width big-endian fields.
        descriptor.extend_from_slice(&limits.message.to_be_bytes());
        descriptor.extend_from_slice(&limits.state.to_be_bytes());
        descriptor.extend_from_slice(&limits.response.to_be_bytes());
        let (log, state) = match mode {
            Mode::Create => {
                let state = Snapshot::load(schema, 0, initial).map_err(state_error)?;
                (
                    Log::create(path, &descriptor, initial).map_err(storage_error)?,
                    state,
                )
            }
            Mode::Open => {
                let (log, recovered) = Log::open(path, &descriptor).map_err(storage_error)?;
                let base_lsn = recovered
                    .commits
                    .first()
                    .map_or(recovered.lsn, |(lsn, _)| lsn - 1);
                let mut state =
                    Snapshot::load(schema, base_lsn, &recovered.state).map_err(state_error)?;
                for (lsn, writes) in recovered.commits {
                    let writes: Vec<_> = writes
                        .into_iter()
                        .map(|entry| (entry.collection, entry.key, entry.row))
                        .collect();
                    state = state.apply_write_set(lsn, &writes).map_err(state_error)?;
                }
                (log, state)
            }
        };
        let log = Arc::new(log);
        let writer = Arc::clone(&log);
        let (checkpoints, queue) = mpsc::sync_channel::<Snapshot>(1);
        let checkpoint_thread = thread::Builder::new()
            .name("jaydb-checkpoint".into())
            .spawn(move || {
                for state in queue {
                    if let Err(error) = writer.checkpoint(state.lsn(), &descriptor, &state.save()) {
                        // The coordinator may be idle waiting for stdin. Stop it
                        // immediately rather than waiting for another request.
                        diagnostic(format_args!("STORAGE_UNCERTAIN: WAL checkpoint: {error}"));
                        std::process::exit(1);
                    }
                }
            })?;
        Ok((
            Self {
                log,
                checkpoints: Some(checkpoints),
                checkpoint_thread: Some(checkpoint_thread),
            },
            state,
        ))
    }

    pub fn append(&self, records: &[Record]) -> Result<()> {
        self.log.append(records).map_err(uncertain)?;
        fault_point("before_publish").map_err(uncertain)
    }

    pub fn checkpoint(&self, previous_lsn: u64, state: &Snapshot) -> Result<()> {
        if previous_lsn / CHECKPOINT_INTERVAL != state.lsn() / CHECKPOINT_INTERVAL {
            let checkpoints = self.checkpoints.as_ref().expect("checkpoint thread active");
            match checkpoints.try_send(state.clone()) {
                Ok(()) | Err(mpsc::TrySendError::Full(_)) => (),
                Err(mpsc::TrySendError::Disconnected(_)) => {
                    return Err(uncertain("checkpoint thread stopped"));
                }
            }
        }
        Ok(())
    }
}

impl Drop for Durable {
    fn drop(&mut self) {
        drop(self.checkpoints.take());
        if let Some(thread) = self.checkpoint_thread.take() {
            let _ = thread.join();
        }
    }
}

fn storage_error(error: io::Error) -> Error {
    Error::new("STORAGE", error.to_string())
}

fn state_error(error: crate::store::StoreError) -> Error {
    Error::new("STORAGE", format!("invalid WAL state: {error}"))
}

pub fn uncertain(error: impl std::fmt::Display) -> Error {
    Error::new("STORAGE_UNCERTAIN", error.to_string())
}
