//! Optional administrator observation; no admission or execution policy.
use serde_json::json;
use std::fs::{File, OpenOptions};
use std::io::{self, Write};
use std::os::unix::fs::OpenOptionsExt;
use std::path::Path;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

pub trait Clock: Send + Sync {
    fn now(&self) -> Duration;
}

struct Monotonic(Instant);
impl Clock for Monotonic {
    fn now(&self) -> Duration {
        self.0.elapsed()
    }
}

enum Sink {
    Stderr,
    File(File),
}
impl Sink {
    fn write(&mut self, bytes: &[u8]) -> io::Result<()> {
        match self {
            Self::Stderr => io::stderr().lock().write_all(bytes),
            Self::File(file) => file.write_all(bytes),
        }
    }
}

pub struct Timing {
    clock: Box<dyn Clock>,
    next: AtomicU64,
    sink: Mutex<Option<Sink>>,
}

/// Owned once from selection through completion, including failed authentication.
pub struct Attempt {
    started: Duration,
    sequence: u64,
    principal: Option<String>,
    read_batch: bool,
}
impl Attempt {
    pub fn authenticated(&mut self, principal: &str) {
        assert!(self.principal.is_none(), "authenticate each attempt once");
        self.principal = Some(principal.to_owned());
    }
}

impl Timing {
    pub fn open(path: &Path) -> io::Result<Self> {
        let sink = if path == Path::new("-") {
            Sink::Stderr
        } else {
            Sink::File(
                OpenOptions::new()
                    .create(true)
                    .append(true)
                    .mode(0o600)
                    .open(path)?,
            )
        };
        Ok(Self {
            clock: Box::new(Monotonic(Instant::now())),
            next: AtomicU64::new(1),
            sink: Mutex::new(Some(sink)),
        })
    }

    pub fn selected(&self, read_batch: bool) -> Attempt {
        Attempt {
            started: self.clock.now(),
            sequence: self.next.fetch_add(1, Ordering::Relaxed),
            principal: None,
            read_batch,
        }
    }

    pub fn completed(&self, attempt: Attempt) {
        // Stamp before serializing or waiting for the log lock, and before any
        // FIFO response wait. A slow administrator sink adds no service time.
        let elapsed = self
            .clock
            .now()
            .checked_sub(attempt.started)
            .expect("monotonic service clock");
        let mut bytes = serde_json::to_vec(&json!({
            "format": "jaydb-service-timing-v1",
            "sequence": attempt.sequence,
            "principal": attempt.principal,
            "elapsed_ns": elapsed.as_nanos().to_string(),
            "read_batch": attempt.read_batch
        }))
        .expect("timing JSON serialization");
        bytes.push(b'\n');
        let mut sink = self.sink.lock().unwrap_or_else(|error| error.into_inner());
        if let Some(output) = &mut *sink
            && let Err(error) = output.write(&bytes)
        {
            eprintln!("jaydb2: TIMING_LOG: {error}");
            *sink = None;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    struct Manual(Arc<AtomicU64>);
    impl Clock for Manual {
        fn now(&self) -> Duration {
            Duration::from_nanos(self.0.load(Ordering::SeqCst))
        }
    }

    #[test]
    fn reverse_completion_preserves_dispatch_identity_and_excludes_delivery() {
        let directory =
            super::super::Temporary::new(&std::env::temp_dir(), "jaydb-timing").unwrap();
        let path = directory.path.join("records");
        let clock = Arc::new(AtomicU64::new(500)); // Queue waiting excluded.
        let timing = Timing {
            clock: Box::new(Manual(clock.clone())),
            next: AtomicU64::new(1),
            sink: Mutex::new(Some(Sink::File(File::create(&path).unwrap()))),
        };
        let mut first = timing.selected(true);
        first.authenticated("alice");
        clock.store(503, Ordering::SeqCst);
        let mut second = timing.selected(true);
        second.authenticated("bob");
        clock.store(518, Ordering::SeqCst);
        timing.completed(second);
        clock.store(540, Ordering::SeqCst);
        timing.completed(first);
        clock.store(999, Ordering::SeqCst); // Delivery does not alter records.
        let records: Vec<serde_json::Value> = std::fs::read_to_string(path)
            .unwrap()
            .lines()
            .map(|line| serde_json::from_str(line).unwrap())
            .collect();
        assert_eq!(records[0]["sequence"], 2);
        assert_eq!(records[0]["elapsed_ns"], "15");
        assert_eq!(records[0]["principal"], "bob");
        assert_eq!(records[1]["sequence"], 1);
        assert_eq!(records[1]["elapsed_ns"], "40");
        assert_eq!(records[1]["principal"], "alice");
    }

    #[test]
    fn empty_identity_and_failed_authentication_remain_distinct() {
        let directory =
            super::super::Temporary::new(&std::env::temp_dir(), "jaydb-timing").unwrap();
        let path = directory.path.join("records");
        let timing = Timing::open(&path).unwrap();
        let mut authenticated = timing.selected(false);
        authenticated.authenticated("");
        timing.completed(authenticated);
        timing.completed(timing.selected(false));
        let records: Vec<serde_json::Value> = std::fs::read_to_string(path)
            .unwrap()
            .lines()
            .map(|line| serde_json::from_str(line).unwrap())
            .collect();
        assert_eq!(records[0]["principal"], "");
        assert!(records[1]["principal"].is_null());
    }
}
