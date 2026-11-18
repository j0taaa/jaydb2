use crate::{Database, Result, diagnostic, error_frame, scheduling};
use std::io;
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::Path;
use std::sync::{Arc, Condvar, Mutex};
use std::thread;

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

pub fn listen(database: Database, path: &Path) -> Result<()> {
    let listener = UnixListener::bind(path)?;
    let database = Arc::new(database);
    for client in listener.incoming() {
        let client = match client {
            Ok(client) => client,
            Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
            Err(error) => return Err(error.into()),
        };
        let database = Arc::clone(&database);
        if let Err(error) = thread::Builder::new()
            .name("jaydb-session".into())
            .spawn(move || serve(&database, client))
        {
            diagnostic(format_args!("SESSION: {error}"));
        }
    }
    Ok(())
}

fn serve(database: &Database, client: UnixStream) {
    let result = scheduling::serve_stream(
        &client,
        database.limits.message,
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
