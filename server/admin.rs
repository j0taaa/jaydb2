//! Owner-only control socket. Each connection carries one migration request.
use crate::{
    Database, Environment, Error, Program, Result, Temporary, diagnostic, error_frame,
    export_schema, json_helper, storage, store, text,
};
use serde_json::{Value, json};
use std::fs;
use std::io::{BufRead, BufReader, Read, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::thread;

pub struct Socket {
    path: PathBuf,
    listener: UnixListener,
}

impl Socket {
    // Called at startup, before any service threads or children exist. The
    // socket has mode 0600 from the moment its pathname becomes visible.
    pub fn bind(path: &Path) -> Result<Self> {
        let mask = unsafe { libc::umask(0o177) };
        let listener = crate::session::bind(path);
        unsafe { libc::umask(mask) };
        Ok(Self {
            path: path.to_owned(),
            listener: listener?,
        })
    }

    pub fn start(&self, database: &Arc<Database>) -> Result<()> {
        let listener = self.listener.try_clone()?;
        let database = Arc::downgrade(database);
        thread::Builder::new()
            .name("jaydb-admin".into())
            .spawn(move || {
                loop {
                    let mut client = crate::session::accept(&listener, "ADMIN");
                    let result = request(&client).and_then(|(configuration, migration)| {
                        let database = database
                            .upgrade()
                            .ok_or_else(|| Error::new("ADMIN", "service is shutting down"))?;
                        database.migrate(Path::new(&configuration), Path::new(&migration))
                    });
                    let response = match result {
                        Ok(lsn) => json!({"status": "success", "lsn": lsn}),
                        Err(error) => {
                            json!({"status": "error", "code": error.code, "message": error.message})
                        }
                    };
                    if let Err(error) = writeln!(client, "{response}") {
                        diagnostic(format_args!("ADMIN: {error}"));
                    }
                }
            })?;
        Ok(())
    }
}

impl Drop for Socket {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

fn request(client: &UnixStream) -> Result<(String, String)> {
    const MAX_LINE: usize = 64 * 1024;
    let mut line = Vec::new();
    BufReader::new(client)
        .take(MAX_LINE as u64 + 1)
        .read_until(b'\n', &mut line)?;
    if line.len() > MAX_LINE || !line.ends_with(b"\n") {
        return Err(Error::new(
            "ADMIN",
            "expected one JSON line of at most 65536 bytes",
        ));
    }
    let input: Value = serde_json::from_slice(&line)?;
    if text(&input, "command")? != "migrate" {
        return Err(Error::new("ADMIN", "unknown administrator command"));
    }
    Ok((
        text(&input, "configuration")?.into(),
        text(&input, "migration")?.into(),
    ))
}

impl Database {
    fn migrate(&self, configuration: &Path, migration: &Path) -> Result<u64> {
        // The admin listener serializes migrations, so the active environment
        // used for checking stays current while clients continue executing.
        let previous = self.active.read().unwrap().path.clone();
        let directory = Temporary::new(&std::env::temp_dir(), "jaydb-migrate")?;
        let report = json_helper(
            &self.stage,
            &[
                "migrate".into(),
                directory.path.clone().into_os_string(),
                previous.into_os_string(),
                fs::canonicalize(configuration)?.into_os_string(),
                fs::canonicalize(migration)?.into_os_string(),
                self.source.clone().into_os_string(),
                self.kernel.clone().into_os_string(),
            ],
        )?;
        let program = Program::load(text(&report, "program")?.into(), 0)?;
        let artifacts = directory.path.join("migrate");
        let environment =
            Environment::load(directory, text(&report, "newEnvironment")?.into(), &report)?;
        let descriptor = environment.descriptor()?;

        let _permit = self.gate.enter(true);
        let mut active = self.active.write().unwrap();
        let current = self.committer.read();
        let lsn = current
            .lsn()
            .checked_add(1)
            .ok_or_else(|| Error::new("ADMIN", "publication sequence exhausted"))?;
        let output = program.run(&current.save(), self.threads)?;
        drop(current);
        let state = migration_state(output)?;
        let schema = export_schema(&report, &environment.limits, self.threads)?;
        let snapshot = store::Snapshot::load(schema, lsn, &state).map_err(|error| match error {
            store::StoreError::Data => rejected("data"),
            store::StoreError::Limit => rejected("limit"),
            _ => Error::new("CONFIGURATION", format!("invalid migrated state: {error}")),
        })?;
        let mut registry = self.registry.write().unwrap();
        let retired = retired_registry(&registry.bytes)?;
        environment.prefill_errors(&snapshot, &retired, self.threads)?;
        fs::remove_dir_all(artifacts)?;

        if let Err(error) = self.committer.publish_epoch(snapshot, descriptor, state) {
            fail_stop(error);
        }
        self.idle_workers.lock().unwrap().clear();
        registry.prepared.clear();
        registry.bytes = retired.into();
        *active = Arc::new(environment);
        if let Err(error) = storage::fault_point("after_publish").map_err(storage::uncertain) {
            fail_stop(error);
        }
        Ok(lsn)
    }
}

fn migration_state(mut output: Vec<u8>) -> Result<Vec<u8>> {
    match output.first() {
        Some(1) => {
            output.remove(0);
            Ok(output)
        }
        Some(0) => {
            for status in ["data", "limit", "failure"] {
                if output[1..] == error_frame(status) {
                    return Err(rejected(status));
                }
            }
            Err(Error::new(
                "HOST_TRANSPORT",
                "invalid migration error response",
            ))
        }
        _ => Err(Error::new("HOST_TRANSPORT", "invalid migration result")),
    }
}

fn rejected(status: &str) -> Error {
    Error::new(status, format!("migration returned {status}"))
}

fn retired_registry(bytes: &[u8]) -> Result<Vec<u8>> {
    // ControlBridge encodes [entries, used]. Drop all entries while retaining
    // the allocation history so a later prepare cannot reuse an old handle.
    if bytes.is_empty() {
        return Ok(Vec::new());
    }
    let invalid = || Error::new("HOST_TRANSPORT", "invalid prepared registry");
    let mut value = store::decode(bytes).map_err(|_| invalid())?;
    let store::Value::List(parts) = &mut value else {
        return Err(invalid());
    };
    let [entries @ store::Value::List(_), store::Value::List(_)] = parts.as_mut_slice() else {
        return Err(invalid());
    };
    *entries = store::Value::List(Vec::new());
    store::encode(&value).map_err(|_| invalid())
}

fn fail_stop(error: Error) -> ! {
    diagnostic(format_args!("{}: {}", error.code, error.message));
    std::process::exit(1);
}
