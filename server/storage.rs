use crate::store::{Schema, Snapshot};
use crate::wal::{Log, Record};
use crate::{Error, Limits, Result};
use std::path::Path;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, mpsc};
use std::thread::{self, JoinHandle};

#[path = "upgrade.rs"]
pub mod upgrade;

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

type Checkpoint = (Snapshot, Arc<Vec<u8>>);

pub struct Durable {
    log: Arc<Log>,
    descriptor: Arc<Vec<u8>>,
    checkpoints: Option<mpsc::SyncSender<Checkpoint>>,
    checkpoint_thread: Option<JoinHandle<()>>,
}

impl Durable {
    pub fn start(
        path: &Path,
        mode: Mode,
        descriptor: Vec<u8>,
        schema: Schema,
        initial: &[u8],
    ) -> Result<(Self, Snapshot)> {
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
        let (checkpoints, queue) = mpsc::sync_channel::<Checkpoint>(1);
        let checkpoint_thread = thread::Builder::new()
            .name("jaydb-checkpoint".into())
            .spawn(move || {
                for (state, descriptor) in queue {
                    if let Err(error) = writer.checkpoint(state.lsn(), &descriptor, &state.save()) {
                        fail_stop(format_args!("WAL checkpoint: {error}"));
                    }
                }
            })?;
        Ok((
            Self {
                log,
                descriptor: Arc::new(descriptor),
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

    pub fn append_epoch(&mut self, lsn: u64, descriptor: Vec<u8>, state: Vec<u8>) -> Result<()> {
        let record = Record::Epoch {
            lsn,
            descriptor,
            state,
        };
        self.append(std::slice::from_ref(&record))?;
        let Record::Epoch { descriptor, .. } = record else {
            unreachable!()
        };
        self.descriptor = Arc::new(descriptor);
        Ok(())
    }

    pub fn checkpoint(&self, previous_lsn: u64, state: &Snapshot) -> Result<()> {
        if previous_lsn / CHECKPOINT_INTERVAL != state.lsn() / CHECKPOINT_INTERVAL {
            let checkpoints = self.checkpoints.as_ref().expect("checkpoint thread active");
            match checkpoints.try_send((state.clone(), Arc::clone(&self.descriptor))) {
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

pub fn descriptor(mut environment: Vec<u8>, limits: &Limits) -> Vec<u8> {
    // Bind the exact frozen environment and the three evaluated limits.
    environment.extend_from_slice(&limits.message.to_be_bytes());
    environment.extend_from_slice(&limits.state.to_be_bytes());
    environment.extend_from_slice(&limits.response.to_be_bytes());
    environment
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

pub fn fail_stop(error: std::fmt::Arguments<'_>) -> ! {
    static STOPPING: AtomicBool = AtomicBool::new(false);

    // Bypass Rust's stderr lock and do not wait for space in a full pipe.
    // Only one failing thread may temporarily change the descriptor flags.
    if !STOPPING.swap(true, Ordering::Relaxed) {
        let message = format!("jaydb2: STORAGE_UNCERTAIN: {error}\n");
        let fd = libc::STDERR_FILENO;
        unsafe {
            let flags = libc::fcntl(fd, libc::F_GETFL);
            if flags >= 0 && libc::fcntl(fd, libc::F_SETFL, flags | libc::O_NONBLOCK) == 0 {
                libc::write(fd, message.as_ptr().cast(), message.len());
                libc::fcntl(fd, libc::F_SETFL, flags);
            }
        }
    }
    // Exit the whole process without running exit handlers or flushing streams.
    unsafe { libc::_exit(1) }
}
