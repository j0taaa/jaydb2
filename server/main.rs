//! Live engine host. Official Bend workers own computation; this process owns publication.
mod admin;
mod capture;
use capture::capture;
mod commit;
use commit::{Committer, Completed, ReadSnapshot};
mod live;
use live::{Decision, Worker};
mod scheduling;
#[cfg(test)]
use scheduling::FrameInput;
#[cfg(test)]
use scheduling::QueueBounds;
use scheduling::{FrameQueue, PollInput};
mod session;
mod storage;
mod store;
mod wal;
use store::{Schema, Snapshot};
mod timing;
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::ffi::{OsStr, OsString};
use std::fs::{self, DirBuilder};
use std::io::{self, Read, Write};
use std::os::unix::fs::DirBuilderExt;
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, RwLock};
use timing::{Attempt, Timing};

type Result<T> = std::result::Result<T, Error>;

// Optional experiment diagnostics; never part of a response or a decision.
fn bench_start() -> Option<std::time::Instant> {
    std::env::var_os("JAYDB_BENCH_TIMING").map(|_| std::time::Instant::now())
}
fn bench_mark(start: &mut Option<std::time::Instant>, phase: &str) {
    if let Some(previous) = start {
        let now = std::time::Instant::now();
        diagnostic(format_args!(
            "JAYDB_BENCH {}",
            serde_json::json!({
                "phase": phase, "ns": now.duration_since(*previous).as_nanos().to_string()
            })
        ));
        *previous = now;
    }
}

// Diagnostics cannot turn an ordinary outcome or disabled observer into a
// panic when the administrator's stderr destination is unavailable.
fn diagnostic(message: std::fmt::Arguments<'_>) {
    let _ = writeln!(io::stderr().lock(), "jaydb2: {message}");
}

#[derive(Clone, Debug)]
struct Error {
    code: String,
    message: String,
}

impl Error {
    fn new(code: &str, message: impl Into<String>) -> Self {
        Self {
            code: code.into(),
            message: message.into(),
        }
    }
}

impl From<io::Error> for Error {
    fn from(error: io::Error) -> Self {
        Self::new("HOST_IO", error.to_string())
    }
}

impl From<serde_json::Error> for Error {
    fn from(error: serde_json::Error) -> Self {
        Self::new("HOST_JSON", error.to_string())
    }
}

struct Temporary {
    path: PathBuf,
    removed: bool,
}

impl Temporary {
    fn new(parent: &Path, prefix: &str) -> Result<Self> {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        loop {
            let path = parent.join(format!(
                "{prefix}-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            match DirBuilder::new().mode(0o700).create(&path) {
                Ok(()) => {
                    return Ok(Self {
                        path,
                        removed: false,
                    });
                }
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
                Err(error) => return Err(error.into()),
            }
        }
    }

    fn remove(&mut self) -> Result<()> {
        fs::remove_dir_all(&self.path)?;
        self.removed = true;
        Ok(())
    }
}

impl Drop for Temporary {
    fn drop(&mut self) {
        if !self.removed {
            let _ = fs::remove_dir_all(&self.path);
        }
    }
}

fn json_helper(script: &Path, arguments: &[OsString]) -> Result<Value> {
    let output = capture(
        Command::new("node")
            .arg("--stack_size=65536")
            .arg(script)
            .args(arguments),
        &[],
    )?;
    if std::env::var_os("JAYDB_BENCH_TIMING").is_some() {
        for line in String::from_utf8_lossy(&output.stderr).lines() {
            if line.starts_with("JAYDB_BENCH ") {
                diagnostic(format_args!("{line}"));
            }
        }
    }
    if output.status.success() {
        return Ok(serde_json::from_slice(&output.stdout)?);
    }
    for data in [&output.stderr, &output.stdout] {
        for line in data.split(|byte| *byte == b'\n').rev() {
            if let Ok(report) = serde_json::from_slice::<Value>(line)
                && let Some(code) = report.get("code").and_then(Value::as_str)
            {
                return Err(Error::new(
                    code,
                    report
                        .get("message")
                        .and_then(Value::as_str)
                        .unwrap_or("compilation failed"),
                ));
            }
        }
    }
    Err(Error::new(
        "HELPER",
        String::from_utf8_lossy(&output.stderr).into_owned(),
    ))
}

fn text<'a>(value: &'a Value, key: &str) -> Result<&'a str> {
    value
        .get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| Error::new("HOST_JSON", format!("missing {key}")))
}

#[derive(PartialEq, Eq)]
struct Limits {
    message: u64,
    state: u64,
    response: u64,
}

impl Limits {
    fn read(value: &Value) -> Result<Self> {
        let object = value
            .get("limits")
            .and_then(Value::as_object)
            .ok_or_else(|| Error::new("HOST_JSON", "missing logical limits"))?;
        if object.len() != 3 {
            return Err(Error::new("HOST_JSON", "expected three logical limits"));
        }
        let number = |key: &str| -> Result<u64> {
            let value = object
                .get(key)
                .ok_or_else(|| Error::new("HOST_JSON", format!("missing {key}")))?;
            if let Some(number) = value.as_u64() {
                return Ok(number);
            }
            value
                .as_str()
                .and_then(|number| number.parse::<u64>().ok())
                .ok_or_else(|| {
                    Error::new(
                        "CONFIGURATION",
                        format!("{key} is outside the uint64 transport domain"),
                    )
                })
        };
        Ok(Self {
            message: number("message")?,
            state: number("state")?,
            response: number("response")?,
        })
    }
}

struct Program {
    path: PathBuf,
    sha256: String,
    gpu: Option<(usize, String)>,
}

impl Program {
    fn load(path: PathBuf, gpu_mib: usize) -> Result<Self> {
        let report: Value = serde_json::from_slice(&fs::read(format!("{}.json", path.display()))?)?;
        if text(&report, "format")? != "jaydb-official-c-v1" {
            return Err(Error::new(
                "HOST_NATIVE",
                "invalid official executable manifest",
            ));
        }
        let expected_backend = if gpu_mib == 0 { "cpu" } else { "cuda" };
        if text(&report, "backend")? != expected_backend {
            return Err(Error::new(
                "HOST_NATIVE",
                "requested/compiled backend mismatch",
            ));
        }
        let gpu = if gpu_mib == 0 {
            if report.get("gpuSha256").is_some() {
                return Err(Error::new("HOST_NATIVE", "unexpected GPU artifact"));
            }
            None
        } else {
            if report.get("gpuMiB").and_then(Value::as_u64) != Some(gpu_mib as u64) {
                return Err(Error::new("HOST_NATIVE", "GPU option/manifest mismatch"));
            }
            Some((gpu_mib, text(&report, "gpuSha256")?.into()))
        };
        let program = Self {
            path,
            gpu,
            sha256: text(&report, "executableSha256")?.into(),
        };
        program.validate()?;
        Ok(program)
    }

    fn validate(&self) -> Result<()> {
        let mut files = vec![(self.path.clone(), &self.sha256)];
        if let Some((_, digest)) = &self.gpu {
            files.push((
                PathBuf::from(format!("{}.gpu", self.path.display())),
                digest,
            ));
        }
        for (path, expected) in files {
            // I/O errors keep their HOST_IO diagnosis, as on main.
            let regular = fs::symlink_metadata(&path)?.file_type().is_file();
            if !regular || format!("{:x}", Sha256::digest(fs::read(&path)?)) != *expected {
                return Err(Error::new(
                    "HOST_NATIVE",
                    format!("changed or nonregular artifact: {}", path.display()),
                ));
            }
        }
        Ok(())
    }

    fn command(&self, threads: usize) -> Command {
        let gpu_option = self
            .gpu
            .as_ref()
            .map(|(mib, _)| format!("{mib}MB"))
            .unwrap_or_else(|| "off".into());
        let mut command = Command::new(&self.path);
        command
            // The host owns runtime policy, including early-exit flags.
            .env("BENDRTS", "")
            .args(["+RTS", "--threads"])
            .arg(threads.to_string())
            .args(["--gpu", &gpu_option, "-RTS"]);
        command
    }

    fn run(&self, input: &[u8], threads: usize) -> Result<Vec<u8>> {
        self.validate()?;
        let output = capture(&mut self.command(threads), input)?;
        if !output.status.success() {
            return Err(Error::new(
                "NATIVE",
                format!(
                    "worker {}: {}",
                    output.status,
                    String::from_utf8_lossy(&output.stderr)
                ),
            ));
        }
        // CUDA only: no success can publish if a bundle changed during
        // execution or if the official runtime rebuilt a device artifact
        // (e.g. device change). The default CPU path keeps its original checks.
        if self.gpu.is_some() {
            self.validate()?;
            if String::from_utf8_lossy(&output.stderr).contains("bend: compiling the GPU program") {
                return Err(Error::new(
                    "GPU_REBUILD",
                    "GPU artifact is incompatible; prepare again",
                ));
            }
        }
        Ok(output.stdout)
    }
}

fn packet(first: &[u8], rest: &[u8]) -> Vec<u8> {
    let mut result = Vec::with_capacity(8 + first.len() + rest.len());
    result.extend_from_slice(&(first.len() as u64).to_be_bytes());
    result.extend_from_slice(first);
    result.extend_from_slice(rest);
    result
}

fn split(data: &[u8]) -> Result<(&[u8], &[u8])> {
    let header: [u8; 8] = data
        .get(..8)
        .and_then(|header| header.try_into().ok())
        .ok_or_else(|| Error::new("HOST_TRANSPORT", "truncated internal length"))?;
    let size = usize::try_from(u64::from_be_bytes(header))
        .map_err(|_| Error::new("HOST_TRANSPORT", "internal length is not representable"))?;
    if size > data.len() - 8 {
        return Err(Error::new("HOST_TRANSPORT", "invalid internal length"));
    }
    Ok((&data[8..8 + size], &data[8 + size..]))
}

fn error_frame(status: &str) -> Vec<u8> {
    response_frame(status, None)
}

fn response_frame(status: &str, value: Option<&str>) -> Vec<u8> {
    fn string(output: &mut Vec<u8>, value: &str) {
        output.push(4);
        output.extend_from_slice(&(value.len() as u64).to_be_bytes());
        output.extend_from_slice(value.as_bytes());
    }
    let mut body = vec![6];
    body.extend_from_slice(&2u64.to_be_bytes());
    string(&mut body, "status");
    string(&mut body, status);
    string(&mut body, "value");
    match value {
        Some(value) => string(&mut body, value),
        None => body.push(0),
    }
    packet(&body, &[])
}

// One entropy candidate retains the ordinary random-handle behavior. After a
// collision, len + 1 distinct counters contain a key absent from len entries.
// The host cardinality fits strictly inside the 256-bit handle namespace.
const _: () = assert!(usize::BITS <= 64);

fn hexadecimal_handle(bytes: [u8; 32]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut handle = String::with_capacity(64);
    for byte in bytes {
        handle.push(DIGITS[(byte >> 4) as usize] as char);
        handle.push(DIGITS[(byte & 15) as usize] as char);
    }
    handle
}

enum ControlDecision {
    Denied(Vec<u8>),
    Add {
        handle: String,
        registry: Vec<u8>,
        response: Vec<u8>,
    },
    Remove {
        handle: String,
        registry: Vec<u8>,
        response: Vec<u8>,
    },
}

struct Database {
    committer: Committer,
    // Reap prepared workers before removing their parent directory.
    registry: RwLock<Registry>,
    active: RwLock<Environment>,
    stage: PathBuf,
    source: PathBuf,
    kernel: PathBuf,
    inspector: Option<Mutex<Inspector>>,
    gate: session::Gate,
    threads: usize,
    timing: Option<Timing>,
    gpu_mib: usize,
}

struct Environment {
    _directory: Temporary,
    path: PathBuf,
    stage: PathBuf,
    authenticate: Program,
    control: Program,
    // Only exact-code replies successfully returned by the checked controller.
    error_replies: Mutex<HashMap<String, Vec<u8>>>,
    limits: Limits,
}

#[derive(Default)]
struct Registry {
    bytes: Vec<u8>,
    prepared: HashMap<String, PreparedProgram>,
}

struct Inspector {
    stream: Option<UnixStream>,
    sequence: u64,
}

#[derive(Default)]
struct WorkerPool {
    idle: Vec<Worker>,
    generation: u64,
}

impl WorkerPool {
    fn retire(&mut self) {
        self.generation = self.generation.wrapping_add(1);
        self.idle.clear();
    }
}

struct PreparedProgram {
    workers: Mutex<WorkerPool>,
    directory: Temporary,
    program: Program,
    original_code: Vec<u8>,
    universal_proof: Vec<u8>,
    // Exact host-owned bytes, not a hash-equality assumption. Rechecking these
    // snapshots does not invoke admission or change the stored certificate.
    sealed: Vec<(PathBuf, Vec<u8>)>,
}

impl PreparedProgram {
    fn seal(directory: &Path) -> Result<Vec<(PathBuf, Vec<u8>)>> {
        let mut files = Vec::new();
        for entry in fs::read_dir(directory)? {
            let entry = entry?;
            if entry.file_type()?.is_dir() {
                files.extend(Self::seal(&entry.path())?);
            } else if entry.file_type()?.is_file() {
                files.push((entry.path(), fs::read(entry.path())?));
            } else {
                return Err(Error::new(
                    "PREPARED_INTEGRITY",
                    "nonregular prepared artifact",
                ));
            }
        }
        Ok(files)
    }

    fn validate(&self) -> Result<()> {
        for (path, expected) in &self.sealed {
            let metadata = fs::symlink_metadata(path)?;
            if !metadata.file_type().is_file() || fs::read(path)? != *expected {
                return Err(Error::new(
                    "PREPARED_INTEGRITY",
                    "sealed prepared artifact changed",
                ));
            }
        }
        Ok(())
    }
}

impl Environment {
    fn load(directory: Temporary, path: PathBuf, report: &Value) -> Result<Self> {
        let programs = programs(report)?;
        Ok(Self {
            _directory: directory,
            path,
            stage: text(report, "stagePath")?.into(),
            authenticate: Program::load(text(programs, "authenticate")?.into(), 0)?,
            control: Program::load(text(programs, "control")?.into(), 0)?,
            error_replies: Mutex::default(),
            limits: Limits::read(report)?,
        })
    }

    fn descriptor(&self) -> Result<Vec<u8>> {
        let bytes = fs::read(self.path.join("environment.bytes"))?;
        Ok(storage::descriptor(bytes, &self.limits))
    }

    fn prefill_errors(&self, snapshot: &Snapshot, registry: &[u8], threads: usize) -> Result<()> {
        // Exact-code denials are independent of state and registry. Keep the
        // generally needed replies available with the controller offline.
        for code in ["HANDLE", "PREPARED_INTEGRITY"] {
            self.checked_error(snapshot, registry, threads, code)?;
        }
        Ok(())
    }

    fn checked_error(
        &self,
        snapshot: &Snapshot,
        registry: &[u8],
        threads: usize,
        code: &str,
    ) -> Result<Vec<u8>> {
        let mut replies = self.error_replies.lock().unwrap();
        if let Some(response) = replies.get(code) {
            diagnostic(format_args!("checked denial memo hit: {code}"));
            return Ok(response.clone());
        }
        diagnostic(format_args!(
            "launching denial controller for exact code: {code}"
        ));
        // Canonical Value text, distinct from preparation's four-field list.
        // No entropy, checker, compiler or prepared artifact runs on this path.
        let mut metadata = vec![4];
        metadata.extend_from_slice(&(code.len() as u64).to_be_bytes());
        metadata.extend_from_slice(code.as_bytes());
        let input = packet(
            &metadata,
            &packet(registry, &packet(&snapshot.authentication_root(None), &[])),
        );
        let output = self.control.run(&input, threads)?;
        if output.first() != Some(&0) {
            return Err(Error::new(
                "HOST_TRANSPORT",
                "invalid checked denial result",
            ));
        }
        let response = &output[1..];
        let (body, trailing) = split(response)?;
        if !trailing.is_empty() || body.len() as u64 > self.limits.response {
            return Err(Error::new(
                "HOST_TRANSPORT",
                "invalid checked denial response",
            ));
        }
        replies.insert(code.to_owned(), response.to_vec());
        Ok(response.to_vec())
    }
}

fn programs(report: &Value) -> Result<&Value> {
    report
        .get("programs")
        .ok_or_else(|| Error::new("HOST_JSON", "missing programs"))
}

fn export_schema(report: &Value, limits: &Limits, threads: usize) -> Result<Schema> {
    let schema = Program::load(text(programs(report)?, "schema")?.into(), 0)?;
    let schema_value = store::decode(&schema.run(&[], threads)?)
        .map_err(|error| Error::new("CONFIGURATION", format!("invalid schema export: {error}")))?;
    Schema::from_value(&schema_value, limits.state)
        .map_err(|error| Error::new("CONFIGURATION", format!("invalid schema: {error}")))
}

impl Database {
    fn initialize(options: Options) -> Result<Self> {
        let recovering = options
            .storage
            .as_ref()
            .is_some_and(|(_, mode)| *mode == storage::Mode::Open);
        // Explicit administrator-only output, separate from the client protocol.
        // UnixStream descriptors are close-on-exec: workers cannot capture it.
        let inspector = options
            .inspect_socket
            .as_ref()
            .map(UnixStream::connect)
            .transpose()?;
        if let Some(stream) = &inspector {
            stream.set_write_timeout(Some(std::time::Duration::from_secs(2)))?;
        }
        let timing = options
            .timing_log
            .as_ref()
            .map(|path| Timing::open(path))
            .transpose()?;
        let directory = Temporary::new(&std::env::temp_dir(), "jaydb2")?;
        let mut arguments = vec![
            if recovering {
                "recover".into()
            } else {
                "initialize".into()
            },
            directory.path.clone().into_os_string(),
            options.configuration.into_os_string(),
        ];
        if let Some(seed) = options.seed {
            arguments.push(seed.into_os_string());
        }
        arguments.extend([
            options.source.clone().into_os_string(),
            options.kernel.clone().into_os_string(),
        ]);
        let stage = options.root.join("tools/service/stage.mjs");
        let report = json_helper(&stage, &arguments)?;
        let initial = Program::load(
            text(
                programs(&report)?,
                if recovering { "recover" } else { "initialize" },
            )?
            .into(),
            0,
        )?;
        let path = directory.path.clone();
        let environment = Environment::load(directory, path, &report)?;
        let limits = &environment.limits;
        let output = initial.run(&[], options.threads)?;
        if output.first() != Some(&1)
            || output.len() as u64 - 1 > limits.state
            || (recovering && output != [1])
        {
            return Err(Error::new(
                "CONFIGURATION",
                "invalid configuration or initial state",
            ));
        }
        let schema = export_schema(&report, limits, options.threads)?;
        let inspection_seed = if inspector.is_some() && !recovering {
            Some(fs::read_to_string(
                environment.path.join("initialize/Seed.bend"),
            )?)
        } else {
            None
        };
        fs::remove_dir_all(environment.path.join(if recovering {
            "recover"
        } else {
            "initialize"
        }))?;
        let (storage, snapshot) = if let Some((path, mode)) = options.storage {
            let descriptor = environment.descriptor()?;
            let (storage, snapshot) =
                storage::Durable::start(&path, mode, descriptor, schema, &output[1..])?;
            (Some(storage), snapshot)
        } else {
            let snapshot = Snapshot::load(schema, 0, &output[1..]).map_err(|error| {
                Error::new("CONFIGURATION", format!("invalid initial state: {error}"))
            })?;
            (None, snapshot)
        };
        environment.prefill_errors(&snapshot, &[], options.threads)?;
        let database = Self {
            committer: Committer::start(snapshot.clone(), storage)?,
            registry: RwLock::default(),
            active: RwLock::new(environment),
            stage,
            source: options.source,
            kernel: options.kernel,
            inspector: inspector.map(|stream| {
                Mutex::new(Inspector {
                    stream: Some(stream),
                    sequence: 0,
                })
            }),
            gate: session::Gate::new(options.concurrency),
            threads: options.threads,
            timing,
            gpu_mib: options.gpu_mib,
        };
        if database.inspector.is_some() {
            let active = database.active.read().unwrap();
            let environment: Value =
                serde_json::from_slice(&fs::read(active.path.join("environment.json"))?)?;
            let mut sources = serde_json::Map::new();
            for entry in fs::read_dir(active.path.join("public"))? {
                let entry = entry?;
                if entry.file_type()?.is_file() {
                    sources.insert(
                        entry.file_name().to_string_lossy().into_owned(),
                        Value::String(fs::read_to_string(entry.path())?),
                    );
                }
            }
            database.inspect(&snapshot, false, serde_json::json!({
                "event": "initialized", "recovered": recovering, "environment": environment, "sources": sources,
                "seed": inspection_seed,
                "limits": {"message": active.limits.message,
                    "state": active.limits.state, "response": active.limits.response}
            }));
        }
        Ok(database)
    }

    fn inspect(&self, snapshot: &Snapshot, completed: bool, mut metadata: Value) {
        if let Some(inspector) = &self.inspector {
            let mut inspector = inspector.lock().unwrap();
            if completed {
                inspector.sequence = inspector.sequence.wrapping_add(1);
            }
            let sequence = inspector.sequence;
            if inspector.stream.is_some() {
                metadata["lsn"] = snapshot.lsn().into();
                inspect_snapshot(&mut inspector.stream, sequence, &snapshot.save(), metadata);
            }
        }
    }

    fn resolve(
        &self,
        snapshot: &ReadSnapshot<'_>,
        proposal: Result<Decision>,
        environment: &Environment,
    ) -> Result<Option<Completed>> {
        match proposal {
            Ok(Decision::Success {
                transaction,
                response,
                commit,
            }) => self
                .committer
                .submit(snapshot, transaction, response, commit),
            Ok(Decision::Keep { response }) => Ok(Some(Completed::new(response, snapshot))),
            Err(error) => {
                diagnostic(format_args!("{}: {}", error.code, error.message));
                let registry = self.registry.read().unwrap();
                let response = environment.checked_error(snapshot, &registry.bytes, self.threads, &error.code).unwrap_or_else(|failure| {
                    diagnostic(format_args!(
                        "denial controller failed for {}: {}: {}; using technical failure fallback (not memoized)",
                        error.code, failure.code, failure.message
                    ));
                    error_frame("failure")
                });
                Ok(Some(Completed::new(response, snapshot)))
            }
        }
    }

    fn preprocess(&self, program: &Program, input: &[u8]) -> Result<Vec<u8>> {
        let output = program.run(input, self.threads)?;
        if !matches!(output.first(), Some(0 | 1 | 3..=5)) {
            return Err(Error::new("HOST_TRANSPORT", "invalid preprocessing result"));
        }
        Ok(output)
    }

    fn propose(
        &self,
        snapshot: &Snapshot,
        environment: &Environment,
        body: &[u8],
        attempt: &mut Option<Attempt>,
        inspection_id: Option<u64>,
    ) -> Result<Decision> {
        let mut bench = bench_start();
        let fields = request_fields(body);
        let credential = fields
            .as_ref()
            .map(|(_, credential, _)| credential.as_str());

        // Rust locates an artifact for an authenticated, well-shaped execution
        // request. The worker still checks the public request, current identity,
        // registry and admitted source/proof before running the program.
        if let ([7, 1, ..], Some((handle, credential, proof))) = (body, &fields)
            && proof.is_empty()
            && let Some(user) = snapshot.authenticate(credential)
        {
            if let Some(attempt) = attempt {
                attempt.authenticated(&user.id);
            }
            bench_mark(&mut bench, "packet_authentication");
            return self.run_prepared(
                snapshot,
                environment,
                handle,
                body,
                &mut bench,
                inspection_id,
            );
        }

        let root = snapshot.authentication_root(credential);
        let input = packet(&root, body);
        let authenticated = self.preprocess(&environment.authenticate, &input)?;
        bench_mark(&mut bench, "packet_authentication");
        if authenticated[0] == 0 {
            return Ok(Decision::Keep {
                response: authenticated[1..].to_vec(),
            });
        }
        let operation = authenticated[0];
        let (principal, metadata) = split(&authenticated[1..])?;
        let principal = std::str::from_utf8(principal)
            .map_err(|_| Error::new("HOST_TRANSPORT", "invalid authenticated principal"))?;
        if let Some(attempt) = attempt {
            attempt.authenticated(principal);
        }
        let (code, rest) = split(metadata)?;
        let (proof, rest) = split(rest)?;
        let (instance, bindings) = split(rest)?;
        if operation == 5 {
            return self.control_operation(&environment.control, &root, body);
        }
        if operation == 4 {
            let handle =
                std::str::from_utf8(code).map_err(|_| Error::new("HANDLE", "invalid handle"))?;
            return self.run_prepared(
                snapshot,
                environment,
                handle,
                body,
                &mut bench,
                inspection_id,
            );
        }
        if self.inspector.is_some() {
            self.inspect(
                snapshot,
                false,
                serde_json::json!({
                    "event": "authenticated", "request": inspection_id,
                    "generated_sources": {
                        "Instance.bend": String::from_utf8_lossy(instance),
                        "Bindings.bend": String::from_utf8_lossy(bindings)
                    }
                }),
            );
        }
        let mut request = Temporary::new(&environment.path, "request")?;
        let metadata = request.path.join("metadata");
        fs::create_dir(&metadata)?;
        for (name, bytes) in [
            ("Client.bend", code),
            ("ClientProof.bend", proof),
            ("Instance.bend", instance),
            ("Bindings.bend", bindings),
        ] {
            fs::write(metadata.join(name), bytes)?;
        }
        let mut arguments: Vec<OsString> = vec![
            if operation == 3 {
                "live-prepare".into()
            } else {
                "live-execute".into()
            },
            environment.path.clone().into_os_string(),
            request.path.clone().into_os_string(),
            metadata.into_os_string(),
            self.source.clone().into_os_string(),
            self.kernel.clone().into_os_string(),
        ];
        if self.gpu_mib != 0 {
            arguments.push(self.gpu_mib.to_string().into());
        }
        let report = json_helper(&environment.stage, &arguments)?;
        if Limits::read(&report)? != environment.limits {
            return Err(Error::new(
                "HOST_TRANSPORT",
                "request configuration changed",
            ));
        }
        let program = Program::load(text(&report, "program")?.into(), self.gpu_mib)?;
        bench_mark(&mut bench, "admission_total");
        if operation == 3 {
            let control = self.run_control(
                &environment.control,
                &root,
                body,
                text(&report, "certificateMode")?,
                code,
                proof,
            )?;
            let (handle, registry, response) = match control {
                ControlDecision::Denied(response) => return Ok(Decision::Keep { response }),
                ControlDecision::Add {
                    handle,
                    registry,
                    response,
                } => (handle, registry, response),
                ControlDecision::Remove { .. } => {
                    return Err(Error::new("HOST_TRANSPORT", "unexpected control removal"));
                }
            };
            let mut sealed = PreparedProgram::seal(&request.path)?;
            sealed.extend(PreparedProgram::seal(&environment.path.join("public"))?);
            sealed.extend(PreparedProgram::seal(&environment.path.join("runtime"))?);
            let mut registered = self.registry.write().unwrap();
            registered.prepared.insert(
                handle,
                PreparedProgram {
                    workers: Mutex::default(),
                    directory: request,
                    program,
                    original_code: code.to_vec(),
                    universal_proof: proof.to_vec(),
                    sealed,
                },
            );
            registered.bytes = registry;
            return Ok(Decision::Keep { response });
        }
        let mut worker = Worker::spawn(&program, self.threads)?;
        let proposal = worker.run(&program, true, body, snapshot, &environment.limits)?;
        bench_mark(&mut bench, "ordinary_worker");
        request.remove()?;
        bench_mark(&mut bench, "proposal_cleanup");
        Ok(proposal)
    }

    fn run_prepared(
        &self,
        snapshot: &Snapshot,
        environment: &Environment,
        handle: &str,
        body: &[u8],
        bench: &mut Option<std::time::Instant>,
        inspection_id: Option<u64>,
    ) -> Result<Decision> {
        let registry = self.registry.read().unwrap();
        let prepared = registry
            .prepared
            .get(handle)
            .ok_or_else(|| Error::new("HANDLE", "unknown or invalidated handle"))?;
        if let Err(error) = prepared.validate() {
            prepared.workers.lock().unwrap().retire();
            return Err(error);
        }
        bench_mark(bench, "prepared_integrity");
        if self.inspector.is_some() {
            let metadata = serde_json::json!({
                "event": "prepared-resolved", "handle": handle, "request": inspection_id,
                "original_code": String::from_utf8_lossy(&prepared.original_code),
                "universal_proof": String::from_utf8_lossy(&prepared.universal_proof)
            });
            self.inspect(snapshot, false, metadata);
        }
        let (idle, generation) = {
            let mut pool = prepared.workers.lock().unwrap();
            (pool.idle.pop(), pool.generation)
        };
        // Every live process here serves a request admitted by the execution
        // gate. If the idle pool is empty, another process fits under its bound.
        let mut worker = match idle {
            Some(worker) => worker,
            None => Worker::spawn(&prepared.program, self.threads)?,
        };
        let input = packet(&registry.bytes, body);
        let proposal = worker.run(
            &prepared.program,
            false,
            &input,
            snapshot,
            &environment.limits,
        )?;
        if prepared.program.gpu.is_some() {
            prepared.validate()?;
        }
        let mut pool = prepared.workers.lock().unwrap();
        if pool.generation == generation {
            pool.idle.push(worker);
        }
        bench_mark(bench, "prepared_worker");
        Ok(proposal)
    }

    fn run_control(
        &self,
        control: &Program,
        root: &[u8],
        body: &[u8],
        mode: &str,
        code: &[u8],
        proof: &[u8],
    ) -> Result<ControlDecision> {
        // Entropy is only a candidate. Control checks shape and lifetime freshness.
        let mut random = [0u8; 32];
        fs::File::open("/dev/urandom")?.read_exact(&mut random)?;
        let candidate = hexadecimal_handle(random);
        let mut metadata = vec![5];
        metadata.extend_from_slice(&4u64.to_be_bytes());
        for field in [candidate.as_bytes(), mode.as_bytes(), code, proof] {
            metadata.push(4);
            metadata.extend_from_slice(&(field.len() as u64).to_be_bytes());
            metadata.extend_from_slice(field);
        }
        let input = packet(
            &metadata,
            &packet(&self.registry.read().unwrap().bytes, &packet(root, body)),
        );
        let output = control.run(&input, self.threads)?;
        match output.first() {
            Some(0) => Ok(ControlDecision::Denied(output[1..].to_vec())),
            Some(tag @ (1 | 3)) => {
                let (handle, rest) = split(&output[1..])?;
                let handle = std::str::from_utf8(handle)
                    .map_err(|_| Error::new("HOST_TRANSPORT", "invalid control handle"))?
                    .to_owned();
                let (registry, response) = split(rest)?;
                let registry = registry.to_vec();
                let response = response.to_vec();
                if *tag == 1 {
                    Ok(ControlDecision::Add {
                        handle,
                        registry,
                        response,
                    })
                } else {
                    Ok(ControlDecision::Remove {
                        handle,
                        registry,
                        response,
                    })
                }
            }
            _ => Err(Error::new(
                "HOST_TRANSPORT",
                "invalid checked control result",
            )),
        }
    }

    fn control_operation(&self, control: &Program, root: &[u8], body: &[u8]) -> Result<Decision> {
        match self.run_control(control, root, body, "", &[], &[])? {
            ControlDecision::Denied(response) => Ok(Decision::Keep { response }),
            ControlDecision::Remove {
                handle,
                registry,
                response,
            } => {
                // Install the checked removal before artifact cleanup: a cleanup
                // failure must never restore execution authority.
                let mut registered = self.registry.write().unwrap();
                registered.bytes = registry;
                match registered.prepared.remove(&handle) {
                    Some(mut artifact) => {
                        artifact.workers.get_mut().unwrap().retire();
                        if let Err(error) = artifact.directory.remove() {
                            diagnostic(format_args!("invalidated artifact cleanup: {error:?}"));
                        }
                    }
                    None => diagnostic(format_args!("invalidated artifact already absent")),
                }
                Ok(Decision::Keep { response })
            }
            ControlDecision::Add { .. } => {
                Err(Error::new("HOST_TRANSPORT", "unexpected control addition"))
            }
        }
    }

    fn message_limit(&self) -> u64 {
        self.active.read().unwrap().limits.message
    }

    fn serve(self: &Arc<Self>) -> Result<()> {
        let database = Arc::clone(self);
        let mut queue =
            FrameQueue::start_dynamic(PollInput(io::stdin()), move || database.message_limit())?;
        serve_queue(&mut queue, &mut io::stdout().lock(), |body| {
            self.request(body)
        })
    }
}

fn inspect_snapshot(
    inspector: &mut Option<UnixStream>,
    sequence: u64,
    state: &[u8],
    mut metadata: Value,
) {
    if let Some(stream) = inspector {
        metadata["sequence"] = sequence.into();
        // Preserve the exact canonical state bytes already owned by the
        // host; the inspector does not compute or publish another state.
        let result = (|| -> io::Result<()> {
            let encoded = serde_json::to_vec(&metadata)?;
            stream.write_all(&packet(&encoded, &[]))?;
            stream.write_all(&packet(state, &[]))?;
            stream.flush()
        })();
        if let Err(error) = result {
            *inspector = None;
            diagnostic(format_args!("INSPECTOR: {error}"));
        }
    }
}

// Read only the routing fields of a canonical public request. Bend still
// validates the envelope and owns all admission and control decisions.
fn request_fields(body: &[u8]) -> Option<(String, String, String)> {
    let body = match body {
        [7, _, payload @ ..] => payload,
        _ => body,
    };
    let request = store::decode(body).ok()?;
    let store::Value::Record(fields) = &request else {
        return None;
    };
    match fields.as_slice() {
        [
            (args, _),
            (code, store::Value::Text(handle)),
            (credential, store::Value::Text(token)),
            (proof, store::Value::Text(certificate)),
        ] if args == "arguments"
            && code == "code"
            && credential == "credential"
            && proof == "proof" =>
        {
            Some((handle.clone(), token.clone(), certificate.clone()))
        }
        _ => None,
    }
}

impl Database {
    // One timing record per request, including retries but excluding delivery.
    fn request(&self, body: &[u8]) -> Result<Vec<u8>> {
        const SHARED_RETRIES: usize = 3;
        static INSPECTION_REQUEST: AtomicU64 = AtomicU64::new(1);

        // Route control opcodes to exclusive execution; checked Dispatch
        // still parses the envelope and decides whether the request is valid.
        let mut exclusive = matches!(body, [7, 0 | 2, ..]);
        let mut permit = self.gate.enter(exclusive);
        let mut attempt = self.timing.as_ref().map(Timing::selected);
        let inspection_id = self
            .inspector
            .as_ref()
            .map(|_| INSPECTION_REQUEST.fetch_add(1, Ordering::Relaxed));
        let mut retries = 0;
        loop {
            let (outcome, diagnostic) = {
                let environment = self.active.read().unwrap();
                // A complete frame may have been read before a limit change.
                if body.len() as u64 > environment.limits.message {
                    return Ok(error_frame("limit"));
                }
                let snapshot = self.committer.read();
                let proposal =
                    self.propose(&snapshot, &environment, body, &mut attempt, inspection_id);
                let diagnostic = proposal
                    .as_ref()
                    .err()
                    .map(|error| serde_json::json!({"code": error.code, "message": error.message}));
                let mut bench = bench_start();
                let outcome = self.resolve(&snapshot, proposal, &environment);
                bench_mark(&mut bench, "publication");
                (outcome, diagnostic)
            };
            match outcome {
                Ok(None) if !exclusive => {
                    retries += 1;
                    if let Some(attempt) = &mut attempt {
                        attempt.retry();
                    }
                    drop(permit);
                    exclusive = retries == SHARED_RETRIES;
                    permit = self.gate.enter(exclusive);
                }
                outcome => {
                    let outcome = outcome.and_then(|completed| {
                        completed.ok_or_else(|| {
                            Error::new("HOST_STORE", "conflict during exclusive execution")
                        })
                    });
                    self.record_timing(attempt, outcome.as_ref().map_or(0, |done| done.wal_batch));
                    let done = outcome?;
                    return self.finish(done, inspection_id, diagnostic);
                }
            }
        }
    }

    fn record_timing(&self, attempt: Option<Attempt>, wal_batch: usize) {
        if let (Some(timing), Some(attempt)) = (&self.timing, attempt) {
            timing.completed(attempt, wal_batch);
        }
    }

    fn finish(
        &self,
        completed: Completed,
        inspection_id: Option<u64>,
        diagnostic: Option<Value>,
    ) -> Result<Vec<u8>> {
        storage::fault_point("after_publish").map_err(storage::uncertain)?;
        if self.inspector.is_some() {
            self.inspect(
                &completed.snapshot,
                true,
                serde_json::json!({
                    "event": "completed", "request": inspection_id, "diagnostic": diagnostic
                }),
            );
        }
        Ok(completed.response)
    }
}

fn serve_queue(
    queue: &mut FrameQueue,
    output: &mut impl Write,
    request: impl FnMut(&[u8]) -> Result<Vec<u8>>,
) -> Result<()> {
    let result = scheduling::coordinate(queue, output, request, error_frame);
    // This also wakes a reader still waiting on an open stdin or queue capacity.
    let cleanup = queue.close();
    result?;
    cleanup?;
    Ok(())
}

struct Options {
    root: PathBuf,
    configuration: PathBuf,
    seed: Option<PathBuf>,
    source: PathBuf,
    kernel: PathBuf,
    inspect_socket: Option<PathBuf>,
    admin_socket: Option<PathBuf>,
    listen: Option<PathBuf>,
    concurrency: usize,
    threads: usize,
    timing_log: Option<PathBuf>,
    storage: Option<(PathBuf, storage::Mode)>,
    gpu_mib: usize,
}

// The pinned official Bend runtime supports up to 128 CPU workers.
const MAX_THREADS: usize = 128;

fn default_threads() -> usize {
    std::thread::available_parallelism()
        .map(|count| count.get())
        .unwrap_or(1)
        .min(MAX_THREADS)
}

fn parse_threads(value: &OsStr) -> Result<usize> {
    parse_count("--threads", value)
}

fn parse_concurrency(value: &OsStr) -> Result<usize> {
    parse_count("--concurrency", value)
}

fn parse_count(option: &str, value: &OsStr) -> Result<usize> {
    value
        .to_str()
        .filter(|text| !text.is_empty() && text.bytes().all(|byte| byte.is_ascii_digit()))
        .and_then(|text| text.parse::<usize>().ok())
        .filter(|count| (1..=MAX_THREADS).contains(count))
        .ok_or_else(|| {
            Error::new(
                "ARGUMENT",
                format!("{option} must be an integer from 1 to 128"),
            )
        })
}

fn parse_gpu(value: &OsStr) -> Result<usize> {
    if value == "off" {
        return Ok(0);
    }
    value
        .to_str()
        .filter(|s| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()))
        .and_then(|s| s.parse::<usize>().ok())
        .filter(|n| (64..=4096).contains(n))
        .ok_or_else(|| {
            Error::new(
                "ARGUMENT",
                "--gpu must be off or an integer MiB from 64 to 4096",
            )
        })
}

impl Options {
    fn read() -> Result<Option<Self>> {
        Self::read_from(std::env::args_os().skip(1))
    }

    fn read_from(arguments: impl IntoIterator<Item = OsString>) -> Result<Option<Self>> {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let lock: Value =
            serde_json::from_str(include_str!("../tools/admission/toolchain.lock.json"))?;
        let mut configuration = None;
        let mut seed = None;
        let mut inspect_socket = None;
        let mut admin_socket = None;
        let mut listen = None;
        let mut concurrency = None;
        let mut threads = None;
        let mut gpu_mib = 0;
        let mut timing_log = None;
        let mut storage = None;
        let mut storage_mode = None;
        let mut source = root.join(format!(".tools/bend-source-{}", text(&lock, "version")?));
        let mut kernel = root.join(format!(".tools/bendtt-{}", text(&lock, "kernelSha256")?));
        let mut arguments = arguments.into_iter();
        while let Some(argument) = arguments.next() {
            if argument == "--help" || argument == "-h" {
                println!(
                    "Usage: jaydb2 --configuration FILE [--seed FILE] [--storage DIRECTORY --storage-mode create|open] [--listen SOCKET] [--concurrency N] [--threads N] [--gpu off|MiB] [--bend-source DIR] [--bendtt FILE] [--inspect-socket INSPECTOR_SOCKET] [--admin-socket SOCKET] [--timing-log FILE|-]\n\n--seed FILE  Required for volatile mode and storage create; forbidden for storage open\n--storage DIRECTORY --storage-mode create|open  Opt-in WAL persistence; create requires a new directory, open requires the current durable environment/executable\n--admin-socket SOCKET  Serve administrator migration requests on an owner-only Unix socket\n--timing-log FILE|-  Administrator elapsed-service NDJSON, - selects stderr\n--listen SOCKET  Serve FIFO sessions on a Unix socket (default: stdin/stdout)\n--concurrency N  Maximum active socket transactions, 1 to 128 (default: available CPUs, capped at 128)\n--threads N  Native CPU workers per process, 1 to 128 (default: 1 for concurrent execution, otherwise available CPUs capped at 128)\n--gpu off|MiB  Official CUDA for ! calls, 64..4096 MiB (default: off); executions stay serial"
                );
                return Ok(None);
            }
            let value = arguments
                .next()
                .ok_or_else(|| Error::new("ARGUMENT", "expected an option value"))?;
            match argument.to_str() {
                Some("--configuration") => configuration = Some(PathBuf::from(value)),
                Some("--seed") => seed = Some(PathBuf::from(value)),
                Some("--bend-source") => source = PathBuf::from(value),
                Some("--bendtt") => kernel = PathBuf::from(value),
                Some("--admin-socket") => admin_socket = Some(PathBuf::from(value)),
                Some("--inspect-socket") => inspect_socket = Some(PathBuf::from(value)),
                Some("--timing-log") => timing_log = Some(PathBuf::from(value)),
                Some("--listen") => listen = Some(PathBuf::from(value)),
                Some("--concurrency") => concurrency = Some(parse_concurrency(&value)?),
                Some("--threads") => threads = Some(parse_threads(&value)?),
                Some("--gpu") => gpu_mib = parse_gpu(&value)?,
                Some("--storage") => storage = Some(PathBuf::from(value)),
                Some("--storage-mode") => {
                    storage_mode = Some(match value.to_str() {
                        Some("create") => storage::Mode::Create,
                        Some("open") => storage::Mode::Open,
                        _ => {
                            return Err(Error::new(
                                "ARGUMENT",
                                "--storage-mode must be create or open",
                            ));
                        }
                    })
                }
                _ => {
                    return Err(Error::new(
                        "ARGUMENT",
                        format!("unknown option {}", argument.to_string_lossy()),
                    ));
                }
            }
        }
        let storage = match (storage, storage_mode) {
            (Some(path), Some(mode)) => Some((path, mode)),
            (None, None) => None,
            _ => {
                return Err(Error::new(
                    "ARGUMENT",
                    "--storage and --storage-mode are required together",
                ));
            }
        };
        let recovering = storage
            .as_ref()
            .is_some_and(|(_, mode)| *mode == storage::Mode::Open);
        if recovering == seed.is_some() {
            return Err(Error::new(
                "ARGUMENT",
                if recovering {
                    "--seed is forbidden for storage open"
                } else {
                    "--seed is required"
                },
            ));
        }
        let concurrency = if listen.is_some() && gpu_mib == 0 {
            concurrency.unwrap_or_else(default_threads)
        } else {
            1
        };
        let threads = threads.unwrap_or_else(|| {
            if concurrency > 1 {
                1
            } else {
                default_threads()
            }
        });
        Ok(Some(Self {
            root,
            configuration: fs::canonicalize(
                configuration
                    .ok_or_else(|| Error::new("ARGUMENT", "--configuration is required"))?,
            )?,
            seed: seed.map(fs::canonicalize).transpose()?,
            source: fs::canonicalize(source)?,
            kernel: fs::canonicalize(kernel)?,
            inspect_socket,
            admin_socket,
            listen,
            concurrency,
            threads,
            timing_log,
            storage,
            gpu_mib,
        }))
    }
}

fn main() {
    let result = (|| -> Result<()> {
        if let Some(options) = Options::read()? {
            let listen = options.listen.clone();
            let admin = options
                .admin_socket
                .as_deref()
                .map(admin::Socket::bind)
                .transpose()?;
            let database = Arc::new(Database::initialize(options)?);
            if let Some(admin) = &admin {
                admin.start(&database)?;
            }
            match listen {
                Some(path) => session::listen(database, &path)?,
                None => database.serve()?,
            }
        }
        Ok(())
    })();
    if let Err(error) = result {
        if error.code == "HOST_IO" && error.message.contains("Broken pipe") {
            return;
        }
        diagnostic(format_args!("{}: {}", error.code, error.message));
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    #[test]
    fn prepared_integrity_keeps_and_checks_exact_original_bytes() {
        let directory = Temporary::new(&std::env::temp_dir(), "jaydb-sealed-bytes").unwrap();
        let path = directory.path.join("artifact");
        let original = b"original prepared artifact";
        fs::write(&path, original).unwrap();
        let sealed = PreparedProgram::seal(&directory.path).unwrap();
        assert_eq!(sealed.len(), 1);
        assert_eq!(sealed[0].0, path);
        assert_eq!(sealed[0].1.as_slice(), original);
        let prepared = PreparedProgram {
            workers: Mutex::default(),
            directory,
            program: Program {
                path: PathBuf::new(),
                sha256: String::new(),
                gpu: None,
            },
            original_code: Vec::new(),
            universal_proof: Vec::new(),
            sealed,
        };
        prepared.validate().unwrap();
        let mut changed = original.to_vec();
        changed[0] ^= 1;
        fs::write(&path, &changed).unwrap();
        assert_eq!(prepared.validate().unwrap_err().code, "PREPARED_INTEGRITY");
        fs::write(&path, original).unwrap();
        prepared.validate().unwrap();
        fs::remove_file(&path).unwrap();
        let replacement = prepared.directory.path.join("replacement");
        fs::write(&replacement, original).unwrap();
        std::os::unix::fs::symlink(&replacement, &path).unwrap();
        assert_eq!(prepared.validate().unwrap_err().code, "PREPARED_INTEGRITY");
    }

    fn serve_stream(
        input: impl FrameInput,
        output: &mut impl Write,
        limit: u64,
        request: impl FnMut(&[u8]) -> Result<Vec<u8>>,
    ) -> Result<()> {
        let mut queue = FrameQueue::start(input, limit, QueueBounds::for_message_limit(limit))?;
        serve_queue(&mut queue, output, request)
    }

    #[test]
    fn thread_options_select_available_cpus_and_allow_explicit_limits() {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let mut arguments = vec![
            "--configuration".into(),
            root.join("examples/access/Configuration.bend")
                .into_os_string(),
            "--seed".into(),
            root.join("examples/access/Seed.bend").into_os_string(),
        ];
        let automatic = Options::read_from(arguments.clone())
            .unwrap()
            .unwrap()
            .threads;
        assert!((1..=MAX_THREADS).contains(&automatic));
        assert_eq!(automatic, default_threads());
        assert_eq!(
            Options::read_from(arguments.clone())
                .unwrap()
                .unwrap()
                .gpu_mib,
            0
        );
        let socket_arguments = [
            arguments.clone(),
            vec![
                "--listen".into(),
                "jaydb.sock".into(),
                "--concurrency".into(),
                "4".into(),
            ],
        ]
        .concat();
        let socket = Options::read_from(socket_arguments.clone())
            .unwrap()
            .unwrap();
        assert_eq!((socket.concurrency, socket.threads), (4, 1));
        let gpu = Options::read_from(
            [
                socket_arguments,
                vec!["--threads".into(), "8".into(), "--gpu".into(), "64".into()],
            ]
            .concat(),
        )
        .unwrap()
        .unwrap();
        assert_eq!((gpu.concurrency, gpu.threads), (1, 8));
        for count in [1, 8, 128] {
            arguments.extend(["--threads".into(), count.to_string().into()]);
            assert_eq!(
                Options::read_from(arguments.clone())
                    .unwrap()
                    .unwrap()
                    .threads,
                count
            );
        }
        for value in [
            "",
            "0",
            "129",
            "-1",
            "+2",
            "1.5",
            " 2",
            "many",
            "18446744073709551616",
        ] {
            let error = Options::read_from(["--threads".into(), value.into()])
                .err()
                .unwrap();
            assert_eq!(error.code, "ARGUMENT");
            assert!(error.message.contains("--threads"));
        }
        assert!(Options::read_from(["--threads".into()]).is_err());
    }

    #[test]
    fn native_launch_forwards_selected_cpu_workers_with_gpu_disabled() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/service/runtime_policy_worker.sh");
        let program = Program {
            sha256: format!("{:x}", Sha256::digest(fs::read(&path).unwrap())),
            path,
            gpu: None,
        };
        for count in [1, 8, 128] {
            assert_eq!(
                program.run(&[], count).unwrap(),
                format!("\n+RTS\n--threads\n{count}\n--gpu\noff\n-RTS\n").as_bytes()
            );
        }
    }

    #[test]
    fn native_runtime_policy_is_not_inherited() {
        const CHILD: &str = "JAYDB_TEST_RTS_POLICY_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let output = Command::new(std::env::current_exe().unwrap())
                .args([
                    "--exact",
                    "tests::native_runtime_policy_is_not_inherited",
                    "--nocapture",
                ])
                .env(CHILD, "1")
                .env("BENDRTS", "--gpu-build --help")
                .output()
                .unwrap();
            assert!(
                output.status.success(),
                "{}{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
            return;
        }
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("tests/service/runtime_policy_worker.sh");
        let program = Program {
            sha256: format!("{:x}", Sha256::digest(fs::read(&path).unwrap())),
            path,
            gpu: None,
        };
        assert_eq!(
            program.run(&[], 1).unwrap(),
            b"\n+RTS\n--threads\n1\n--gpu\noff\n-RTS\n"
        );
    }

    #[test]
    fn gpu_option_is_explicit_bounded_and_defaults_off() {
        assert_eq!(parse_gpu(OsStr::new("off")).unwrap(), 0);
        for count in [64, 512, 4096] {
            assert_eq!(parse_gpu(OsStr::new(&count.to_string())).unwrap(), count);
        }
        for value in [
            "on", "auto", "0", "63", "4097", "-1", "64MB", "1.5", "+512", "",
        ] {
            assert!(parse_gpu(OsStr::new(value)).is_err());
        }
    }

    #[test]
    fn gpu_bundle_requires_both_exact_regular_files() {
        let directory = Temporary::new(&std::env::temp_dir(), "jaydb-gpu-test").unwrap();
        let path = directory.path.join("worker");
        let device = directory.path.join("worker.gpu");
        fs::write(&path, b"native").unwrap();
        fs::write(&device, b"device").unwrap();
        let program = Program {
            sha256: format!("{:x}", Sha256::digest(b"native")),
            gpu: Some((512, format!("{:x}", Sha256::digest(b"device")))),
            path,
        };
        program.validate().unwrap();
        for (file, original) in [
            (&program.path, b"native".as_slice()),
            (&device, b"device".as_slice()),
        ] {
            fs::write(file, b"substitute").unwrap();
            assert!(program.validate().is_err());
            fs::remove_file(file).unwrap();
            assert!(program.validate().is_err());
            fs::write(file, original).unwrap();
        }
        fs::remove_file(&device).unwrap();
        let identical = directory.path.join("identical");
        fs::write(&identical, b"device").unwrap();
        std::os::unix::fs::symlink(identical, &device).unwrap();
        assert!(program.validate().is_err());
    }

    #[test]
    fn program_load_rejects_backend_and_corpus_mismatch() {
        let directory = Temporary::new(&std::env::temp_dir(), "jaydb-gpu-load").unwrap();
        let path = directory.path.join("worker");
        fs::write(&path, b"native").unwrap();
        fs::write(directory.path.join("worker.gpu"), b"device").unwrap();
        let native = format!("{:x}", Sha256::digest(b"native"));
        let device = format!("{:x}", Sha256::digest(b"device"));
        let report = |value: Value| {
            fs::write(format!("{}.json", path.display()), value.to_string()).unwrap();
        };
        let cpu = serde_json::json!({"format": "jaydb-official-c-v1", "backend": "cpu", "executableSha256": native});
        let cuda = serde_json::json!({"format": "jaydb-official-c-v1", "backend": "cuda",
            "executableSha256": native, "gpuSha256": device, "gpuMiB": 512});
        report(cpu.clone());
        assert!(Program::load(path.clone(), 0).unwrap().gpu.is_none());
        assert!(Program::load(path.clone(), 512).is_err());
        report(cuda.clone());
        assert_eq!(
            Program::load(path.clone(), 512).unwrap().gpu,
            Some((512, device.clone()))
        );
        assert!(Program::load(path.clone(), 0).is_err());
        assert!(Program::load(path.clone(), 1024).is_err());
        let mut smuggled = cpu;
        smuggled["gpuSha256"] = Value::String(device);
        report(smuggled);
        assert!(Program::load(path.clone(), 0).is_err());
    }

    fn hex(value: &str) -> Vec<u8> {
        value
            .as_bytes()
            .as_chunks::<2>()
            .0
            .iter()
            .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap())
            .collect()
    }

    #[test]
    fn fixed_errors_match_the_proved_canonical_frames() {
        assert_eq!(
            error_frame("input"),
            hex(
                "0000000000000035060000000000000002040000000000000006737461747573040000000000000005696e70757404000000000000000576616c756500"
            )
        );
        assert_eq!(
            error_frame("failure"),
            hex(
                "00000000000000370600000000000000020400000000000000067374617475730400000000000000076661696c75726504000000000000000576616c756500"
            )
        );
        assert!(split(&[0; 7]).is_err());
        assert!(split(&8u64.to_be_bytes()).is_err());
    }

    #[test]
    fn framing_preserves_the_next_request_and_stops_on_unknown_extent() {
        let mut seen = Vec::new();
        let mut response = Vec::new();
        let incoming = packet(b"bad", &packet(b"next", &[]));
        serve_stream(Cursor::new(incoming), &mut response, 4, |body| {
            seen.push(body.to_vec());
            Ok(error_frame(if body == b"bad" {
                "input"
            } else {
                "refusal"
            }))
        })
        .unwrap();
        assert_eq!(seen, [b"bad".to_vec(), b"next".to_vec()]);
        assert_eq!(
            response,
            [error_frame("input"), error_frame("refusal")].concat()
        );
        for (incoming, status) in [
            (vec![0; 7], "input"),
            (5u64.to_be_bytes().to_vec(), "limit"),
            (packet(b"four", &[])[..9].to_vec(), "input"),
        ] {
            let mut response = Vec::new();
            serve_stream(Cursor::new(incoming), &mut response, 4, |_| {
                panic!("incomplete request reached execution")
            })
            .unwrap();
            assert_eq!(response, error_frame(status));
        }
    }

    #[test]
    fn delivery_failure_after_publication_does_not_undo_the_state() {
        struct BrokenOutput;
        impl Write for BrokenOutput {
            fn write(&mut self, _: &[u8]) -> io::Result<usize> {
                Err(io::ErrorKind::BrokenPipe.into())
            }
            fn flush(&mut self) -> io::Result<()> {
                Ok(())
            }
        }
        let mut snapshot = empty_test_snapshot();
        let result = serve_stream(
            Cursor::new(packet(b"call", &[])),
            &mut BrokenOutput,
            4,
            |_| {
                snapshot = test_write(&snapshot).commit(&snapshot, 1).unwrap();
                Ok(error_frame("success"))
            },
        );
        assert!(result.is_err());
        assert!(snapshot.authenticate("new-token").is_some());
    }

    fn empty_test_snapshot() -> Snapshot {
        Snapshot::empty(Schema::new(Vec::new(), 1024).unwrap(), 0).unwrap()
    }

    fn test_write(snapshot: &Snapshot) -> store::Transaction {
        let mut transaction = snapshot.begin();
        let fields = [
            ("credential", "new-token"),
            ("id", "user"),
            ("kind", "user"),
        ]
        .map(|(key, value)| (key.into(), store::Value::Text(value.into())));
        assert_eq!(
            transaction.operate(store::Operation::DefineRow {
                collection: None,
                key: "user".into(),
                fields: fields.into(),
            }),
            store::Answer::Changed
        );
        transaction
    }

    #[test]
    fn fatal_publication_emits_nothing_and_never_dispatches_the_next_frame() {
        let incoming = [packet(b"commit", &[]), packet(b"later", &[])].concat();
        let mut output = Vec::new();
        let mut calls = 0;
        let error = serve_stream(Cursor::new(incoming), &mut output, 10, |body| {
            calls += 1;
            assert_eq!(body, b"commit");
            Err(Error::new("STORAGE_UNCERTAIN", "directory sync failed"))
        })
        .unwrap_err();
        assert_eq!(error.code, "STORAGE_UNCERTAIN");
        assert_eq!(calls, 1);
        assert!(output.is_empty());
    }

    #[test]
    fn checkpoints_after_an_epoch_use_its_descriptor() {
        let directory = Temporary::new(&std::env::temp_dir(), "jaydb-epoch").unwrap();
        let path = directory.path.join("db");
        let schema = || Schema::new(Vec::new(), 1024).unwrap();
        let initial = empty_test_snapshot().save();
        let (storage, snapshot) = storage::Durable::start(
            &path,
            storage::Mode::Create,
            b"old".to_vec(),
            schema(),
            &initial,
        )
        .unwrap();
        let committer = Committer::start(snapshot, Some(storage)).unwrap();
        let epoch = Snapshot::load(schema(), 1, &initial).unwrap();
        committer
            .publish_epoch(epoch, b"new".to_vec(), initial)
            .unwrap();
        for lsn in 2..=257 {
            let snapshot = committer.read();
            let completed = committer
                .submit(&snapshot, test_write(&snapshot), Vec::new(), true)
                .unwrap()
                .unwrap();
            assert_eq!(completed.snapshot.lsn(), lsn);
        }
        drop(committer); // Wait for the background checkpoint.
        assert!(path.join("checkpoint-256").is_file());
        let (_storage, recovered) =
            storage::Durable::start(&path, storage::Mode::Open, b"new".to_vec(), schema(), &[])
                .unwrap();
        assert_eq!(recovered.lsn(), 257);
        assert!(recovered.authenticate("new-token").is_some());
    }

    #[test]
    fn result_ready_follows_commit_and_precedes_final_inspector_output() {
        let directory = Temporary::new(&std::env::temp_dir(), "jaydb-ready").unwrap();
        let path = directory.path.join("db");
        let limits = Limits {
            message: 100,
            state: 1024,
            response: 100,
        };
        let initial = empty_test_snapshot().save();
        let (storage, snapshot) = storage::Durable::start(
            &path,
            storage::Mode::Create,
            storage::descriptor(b"test environment".to_vec(), &limits),
            Schema::new(Vec::new(), limits.state).unwrap(),
            &initial,
        )
        .unwrap();
        let (inspector, mut observer) = UnixStream::pair().unwrap();
        observer.set_nonblocking(true).unwrap();
        let mut db = Database {
            committer: Committer::start(snapshot, Some(storage)).unwrap(),
            registry: RwLock::default(),
            active: RwLock::new(Environment {
                path: directory.path.clone(),
                _directory: directory,
                stage: PathBuf::new(),
                authenticate: Program {
                    path: PathBuf::new(),
                    sha256: String::new(),
                    gpu: None,
                },
                control: Program {
                    path: PathBuf::new(),
                    sha256: String::new(),
                    gpu: None,
                },
                error_replies: Mutex::default(),
                limits,
            }),
            stage: PathBuf::new(),
            source: PathBuf::new(),
            kernel: PathBuf::new(),
            inspector: Some(Mutex::new(Inspector {
                stream: Some(inspector),
                sequence: u64::MAX,
            })),
            gate: session::Gate::new(1),
            threads: 1,
            timing: None,
            gpu_mib: 0,
        };
        let response = error_frame("success");
        let snapshot = db.committer.read();
        let transaction = test_write(&snapshot);
        let completed = db
            .resolve(
                &snapshot,
                Ok(Decision::Success {
                    transaction,
                    response: response.clone(),
                    commit: true,
                }),
                &db.active.read().unwrap(),
            )
            .unwrap()
            .unwrap();
        drop(snapshot);
        assert!(path.join("segment-1").metadata().unwrap().len() > 0);
        assert_eq!(
            observer.read(&mut [0]).unwrap_err().kind(),
            io::ErrorKind::WouldBlock
        );
        assert_eq!(db.finish(completed, None, None).unwrap(), response);
        let committed = db.committer.read().save();
        assert!(db.committer.read().authenticate("new-token").is_some());
        assert_eq!(db.inspector.as_ref().unwrap().lock().unwrap().sequence, 0);
        let volatile = Committer::start(db.committer.read().clone(), None).unwrap();
        drop(std::mem::replace(&mut db.committer, volatile));
        let limits = &db.active.get_mut().unwrap().limits;
        let (_reopened, recovered) = storage::Durable::start(
            &path,
            storage::Mode::Open,
            storage::descriptor(b"test environment".to_vec(), limits),
            Schema::new(Vec::new(), limits.state).unwrap(),
            &[],
        )
        .unwrap();
        assert_eq!(recovered.save(), committed);
        assert!(observer.read(&mut [0; 1024]).unwrap() > 0);

        // The host must forward the controller's bytes, even when a test
        // executable returns a different status from the old Rust table.
        use std::os::unix::fs::PermissionsExt;
        let executable = db.active.get_mut().unwrap().path.join("denial");
        let script = b"#!/bin/sh\ncat > \"$0.input\"\ncat \"$0.reply\"\n";
        fs::write(&executable, script).unwrap();
        fs::set_permissions(&executable, fs::Permissions::from_mode(0o700)).unwrap();
        db.active.get_mut().unwrap().control = Program {
            path: executable.clone(),
            sha256: format!("{:x}", Sha256::digest(script)),
            gpu: None,
        };
        let forwarded = error_frame("opaque-denial");
        fs::write(
            executable.with_extension("reply"),
            [vec![0], forwarded.clone()].concat(),
        )
        .unwrap();
        for code in ["PRIMARY_CHECK", "HANDLE", "PREPARED_INTEGRITY"] {
            assert_eq!(
                publish(&db, Err(Error::new(code, "test failure"))).unwrap(),
                forwarded
            );
            assert_eq!(db.committer.read().save(), committed);
            let input = fs::read(executable.with_extension("input")).unwrap();
            let (metadata, rest) = split(&input).unwrap();
            let mut expected = vec![4];
            expected.extend_from_slice(&(code.len() as u64).to_be_bytes());
            expected.extend_from_slice(code.as_bytes());
            assert_eq!(metadata, expected);
            let (registry, rest) = split(rest).unwrap();
            assert_eq!(registry, db.registry.read().unwrap().bytes);
            let (root, body) = split(rest).unwrap();
            assert_eq!(root, initial);
            assert!(body.is_empty());
            assert!(observer.read(&mut [0; 1024]).unwrap() > 0);
        }
        // A broken denial ABI cannot introduce a Commit. Failure of the
        // denial machinery itself uses the existing technical fallback.
        fs::write(
            executable.with_extension("reply"),
            [vec![1], packet(b"bad", &response)].concat(),
        )
        .unwrap();
        assert_eq!(
            publish(&db, Err(Error::new("HOST_IO", "rejected"))).unwrap(),
            error_frame("failure")
        );
        assert_eq!(db.committer.read().save(), committed);
        assert!(observer.read(&mut [0; 1024]).unwrap() > 0);
        assert!(
            !db.active
                .read()
                .unwrap()
                .error_replies
                .lock()
                .unwrap()
                .contains_key("HOST_IO")
        );
        // A later successful exact-code reply must replace neither a prepared
        // entry nor a fallback; only this checked reply is memoized.
        let host_io_reply = error_frame("host-io-specific");
        fs::write(
            executable.with_extension("reply"),
            [vec![0], host_io_reply.clone()].concat(),
        )
        .unwrap();
        assert_eq!(
            publish(&db, Err(Error::new("HOST_IO", "retry"))).unwrap(),
            host_io_reply
        );
        let input = fs::read(executable.with_extension("input")).unwrap();
        let (metadata, _) = split(&input).unwrap();
        assert_eq!(metadata, [vec![4], packet(b"HOST_IO", &[])].concat());
        assert!(observer.read(&mut [0; 1024]).unwrap() > 0);
        fs::remove_file(&executable).unwrap();
        for _ in 0..2 {
            assert_eq!(
                publish(&db, Err(Error::new("UNSEEN_CODE", "rejected"))).unwrap(),
                error_frame("failure")
            );
            assert_eq!(db.committer.read().save(), committed);
            assert!(observer.read(&mut [0; 1024]).unwrap() > 0);
            assert!(
                !db.active
                    .read()
                    .unwrap()
                    .error_replies
                    .lock()
                    .unwrap()
                    .contains_key("UNSEEN_CODE")
            );
        }
        assert_eq!(
            publish(&db, Err(Error::new("HOST_IO", "memoized"))).unwrap(),
            host_io_reply
        );
        assert!(observer.read(&mut [0; 1024]).unwrap() > 0);
        for code in ["PRIMARY_CHECK", "HANDLE", "PREPARED_INTEGRITY"] {
            let error = Error::new(code, "physical prepared failure");
            assert_eq!(publish(&db, Err(error)).unwrap(), forwarded);
            assert_eq!(db.committer.read().save(), committed);
            assert!(observer.read(&mut [0; 1024]).unwrap() > 0);
        }
    }

    fn publish(db: &Database, proposal: Result<Decision>) -> Result<Vec<u8>> {
        let snapshot = db.committer.read();
        let completed = db
            .resolve(&snapshot, proposal, &db.active.read().unwrap())?
            .unwrap();
        db.finish(completed, None, None)
    }

    #[test]
    fn helpers_drain_binary_pipes_and_are_reaped_on_failure() {
        let bytes: Vec<u8> = (0..262144).map(|value| value as u8).collect();
        let output = capture(
            Command::new("/bin/sh").args(["-c", "cat; head -c 131072 /dev/zero >&2"]),
            &bytes,
        )
        .unwrap();
        assert!(output.status.success());
        assert_eq!(output.stdout, bytes);
        assert_eq!(output.stderr, vec![0; 131072]);
        let output = capture(
            Command::new("/bin/sh").args(["-c", "printf '%s' \"$$\"; exit 4"]),
            &bytes,
        )
        .unwrap();
        assert_eq!(output.status.code(), Some(4));
        let pid = std::str::from_utf8(&output.stdout).unwrap();
        assert!(
            !Path::new(&format!("/proc/{pid}")).exists(),
            "failed child was not reaped"
        );
    }
}
