use crate::{Database, Result, diagnostic, error_frame, scheduling};
use std::ffi::c_char;
use std::fs::{self, File, OpenOptions, TryLockError};
use std::io;
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{FileTypeExt, MetadataExt, OpenOptionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::thread;
use std::time::Duration;

/// Admission for execution and commit, with FIFO priority for exclusive work.
pub struct Gate {
    limit: usize,
    state: Mutex<State>,
    changed: Condvar,
}

#[derive(Default)]
struct State {
    active: usize,
    next_exclusive: u64,
    serving_exclusive: u64,
}

pub struct Permit<'a> {
    gate: &'a Gate,
    exclusive: bool,
}

impl Gate {
    pub fn new(limit: usize) -> Self {
        Self {
            limit,
            state: Mutex::new(State::default()),
            changed: Condvar::new(),
        }
    }

    pub fn enter(&self, exclusive: bool) -> Permit<'_> {
        let mut state = self.state.lock().unwrap();
        if exclusive {
            let ticket = state.next_exclusive;
            state.next_exclusive = ticket.wrapping_add(1);
            while state.active != 0 || state.serving_exclusive != ticket {
                state = self.changed.wait(state).unwrap();
            }
        } else {
            while state.active == self.limit || state.serving_exclusive != state.next_exclusive {
                state = self.changed.wait(state).unwrap();
            }
        }
        state.active += 1;
        Permit {
            gate: self,
            exclusive,
        }
    }
}

impl Drop for Permit<'_> {
    fn drop(&mut self) {
        let mut state = self.gate.state.lock().unwrap();
        state.active -= 1;
        if self.exclusive {
            state.serving_exclusive = state.serving_exclusive.wrapping_add(1);
        }
        self.gate.changed.notify_all();
    }
}

const MAX_SESSIONS: usize = 128;

struct SessionSlot(Arc<AtomicUsize>);

impl SessionSlot {
    fn acquire(active: &Arc<AtomicUsize>) -> Option<Self> {
        active
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |count| {
                (count < MAX_SESSIONS).then_some(count + 1)
            })
            .ok()
            .map(|_| Self(Arc::clone(active)))
    }
}

impl Drop for SessionSlot {
    fn drop(&mut self) {
        self.0.fetch_sub(1, Ordering::Relaxed);
    }
}

pub fn listen(database: Arc<Database>, path: &Path) -> Result<()> {
    let listener = bind(path)?;
    let active = Arc::new(AtomicUsize::new(0));
    loop {
        let client = listener.accept("SESSION");
        let Some(slot) = SessionSlot::acquire(&active) else {
            continue; // Dropping the socket refuses this session.
        };
        let database = Arc::clone(&database);
        if let Err(error) = thread::Builder::new()
            .name("jaydb-session".into())
            .spawn(move || {
                let _slot = slot;
                serve(&database, client);
            })
        {
            diagnostic(format_args!("SESSION: {error}"));
        }
    }
}

#[derive(Debug)]
pub struct Listener {
    socket: UnixListener,
    _lock: SocketLock,
}

#[derive(Debug)]
struct SocketLock(File);

impl Drop for SocketLock {
    fn drop(&mut self) {
        // The listener is closed first. Release the lock even if a forked
        // helper still shares the file description before its exec.
        let _ = self.0.unlock();
    }
}

impl Listener {
    pub fn accept(&self, service: &str) -> UnixStream {
        loop {
            match self.socket.accept() {
                Ok((client, _)) => return client,
                Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                Err(error) => {
                    diagnostic(format_args!("{service} accept: {error}"));
                    thread::sleep(Duration::from_millis(50));
                }
            }
        }
    }
}

pub fn bind(path: &Path) -> io::Result<Listener> {
    let mut lock_path = path.as_os_str().to_os_string();
    lock_path.push(".lock");
    // Keep the lock file at this pathname so every starter locks the same inode.
    let lock = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK)
        .open(lock_path)?;
    if !lock.metadata()?.is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "nonregular socket lock file",
        ));
    }
    lock.try_lock().map_err(|error| match error {
        TryLockError::WouldBlock => {
            io::Error::new(io::ErrorKind::AddrInUse, "socket path is locked")
        }
        TryLockError::Error(error) => error,
    })?;
    let lock = SocketLock(lock);
    let socket = bind_or_reclaim(path)?;
    Ok(Listener {
        socket,
        _lock: lock,
    })
}

fn bind_or_reclaim(path: &Path) -> io::Result<UnixListener> {
    let occupied = match UnixListener::bind(path) {
        Err(error) if error.kind() == io::ErrorKind::AddrInUse => error,
        result => return result,
    };
    let existing = fs::symlink_metadata(path)?;
    if !existing.file_type().is_socket() || !connection_refused(path)? {
        return Err(occupied);
    }
    let current = fs::symlink_metadata(path)?;
    if (current.dev(), current.ino()) != (existing.dev(), existing.ino()) {
        return Err(occupied);
    }
    fs::remove_file(path)?;
    UnixListener::bind(path)
}

fn connection_refused(path: &Path) -> io::Result<bool> {
    // A full backlog on a live socket must not block startup.
    let fd = unsafe {
        libc::socket(
            libc::AF_UNIX,
            libc::SOCK_STREAM | libc::SOCK_NONBLOCK | libc::SOCK_CLOEXEC,
            0,
        )
    };
    if fd == -1 {
        return Err(io::Error::last_os_error());
    }
    let fd = unsafe { OwnedFd::from_raw_fd(fd) };
    // bind already checked the pathname length and absence of NUL bytes.
    let mut address: libc::sockaddr_un = unsafe { std::mem::zeroed() };
    address.sun_family = libc::AF_UNIX as libc::sa_family_t;
    for (slot, &byte) in address.sun_path.iter_mut().zip(path.as_os_str().as_bytes()) {
        *slot = byte as c_char;
    }
    let result = unsafe {
        libc::connect(
            fd.as_raw_fd(),
            (&raw const address).cast(),
            std::mem::size_of_val(&address) as libc::socklen_t,
        )
    };
    Ok(result == -1 && io::Error::last_os_error().raw_os_error() == Some(libc::ECONNREFUSED))
}

fn serve(database: &Database, client: UnixStream) {
    let result = scheduling::serve_stream(
        &client,
        || database.message_limit(),
        |body| database.request(body),
        error_frame,
    );
    if let Err(error) = result {
        diagnostic(format_args!("{}: {}", error.code, error.message));
        if matches!(error.code.as_str(), "STORAGE_UNCERTAIN" | "HOST_STORE") {
            std::process::exit(1);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn live_sessions_are_capped_and_released_on_close() {
        let active = Arc::new(AtomicUsize::new(0));
        let mut sessions: Vec<_> = (0..MAX_SESSIONS)
            .map(|_| SessionSlot::acquire(&active).unwrap())
            .collect();
        assert!(SessionSlot::acquire(&active).is_none());
        drop(sessions.pop());
        sessions.push(SessionSlot::acquire(&active).unwrap());
        assert!(SessionSlot::acquire(&active).is_none());
        drop(sessions);
        assert_eq!(active.load(Ordering::Relaxed), 0);
    }

    #[test]
    fn bind_reclaims_only_stale_socket_paths() {
        let directory = crate::Temporary::new(&std::env::temp_dir(), "jaydb-socket").unwrap();
        let path = directory.path.join("service.sock");
        let listener = bind(&path).unwrap();
        assert_eq!(bind(&path).unwrap_err().kind(), io::ErrorKind::AddrInUse);
        UnixStream::connect(&path).unwrap();
        listener.socket.accept().unwrap();
        drop(listener);
        drop(bind(&path).unwrap());

        fs::remove_file(&path).unwrap();
        fs::write(&path, b"keep").unwrap();
        assert_eq!(bind(&path).unwrap_err().kind(), io::ErrorKind::AddrInUse);
        assert_eq!(fs::read(&path).unwrap(), b"keep");

        fs::remove_file(&path).unwrap();
        let target = directory.path.join("stale.sock");
        drop(bind(&target).unwrap());
        std::os::unix::fs::symlink(&target, &path).unwrap();
        assert_eq!(bind(&path).unwrap_err().kind(), io::ErrorKind::AddrInUse);
        assert_eq!(fs::read_link(&path).unwrap(), target);
    }

    #[test]
    fn only_one_concurrent_starter_reclaims_a_stale_socket() {
        let directory = crate::Temporary::new(&std::env::temp_dir(), "jaydb-socket-race").unwrap();
        let path = directory.path.join("service.sock");
        drop(UnixListener::bind(&path).unwrap());
        let start = std::sync::Barrier::new(8);
        let results = thread::scope(|scope| {
            let starters: Vec<_> = (0..8)
                .map(|_| {
                    scope.spawn(|| {
                        start.wait();
                        bind(&path)
                    })
                })
                .collect();
            starters
                .into_iter()
                .map(|starter| starter.join().unwrap())
                .collect::<Vec<_>>()
        });
        let mut listeners = Vec::new();
        for result in results {
            match result {
                Ok(listener) => listeners.push(listener),
                Err(error) => assert_eq!(error.kind(), io::ErrorKind::AddrInUse),
            }
        }
        assert_eq!(listeners.len(), 1);
        UnixStream::connect(&path).unwrap();
        listeners[0].socket.accept().unwrap();
    }
}
