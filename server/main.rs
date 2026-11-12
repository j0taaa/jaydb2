//! Serial host. Official Bend workers own computation; this process owns publication.
mod capture;
use capture::capture;
mod scheduling;
use scheduling::FrameInput;
use scheduling::{FrameQueue, PollInput, QueueBounds};
mod storage;
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
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
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

#[derive(Debug)]
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
                    format!("missing or changed artifact: {}", path.display()),
                ));
            }
        }
        Ok(())
    }

    fn run(&self, input: &[u8], threads: usize) -> Result<Vec<u8>> {
        self.validate()?;
        let gpu_option = self
            .gpu
            .as_ref()
            .map(|(mib, _)| format!("{mib}MB"))
            .unwrap_or_else(|| "off".into());
        let output = capture(
            Command::new(&self.path)
                // The host owns runtime policy, including early-exit flags.
                .env("BENDRTS", "")
                .args(["+RTS", "--threads"])
                .arg(threads.to_string())
                .args(["--gpu", &gpu_option, "-RTS"]),
            input,
        )?;
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

fn packet(state: &[u8], body: &[u8]) -> Vec<u8> {
    let mut result = Vec::new();
    result.extend_from_slice(&(state.len() as u64).to_be_bytes());
    result.extend_from_slice(state);
    result.extend_from_slice(body);
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

// Exact checked worker decision; Rust never derives publication from status.
enum Decision {
    Commit { state: Vec<u8>, response: Vec<u8> },
    Keep { response: Vec<u8> },
}

struct Published {
    state: Vec<u8>,
    response: Vec<u8>,
}

impl Published {
    fn finish(&mut self, proposal: Decision) -> Vec<u8> {
        match proposal {
            Decision::Commit { state, response } => {
                // Both values and all cleanup are complete before this store.
                *self = Self { state, response };
                self.response.clone()
            }
            Decision::Keep { response } => response,
        }
    }
}

// Framing/size checks here defend the private ABI against corruption.
// Gate.finish already decided limits, status, publication and exact bytes.
fn parse_decision(output: &[u8], limits: &Limits) -> Result<Decision> {
    let (state, response) = match output.first() {
        Some(1) => {
            let (state, response) = split(&output[1..])?;
            (Some(state), response)
        }
        Some(0) => (None, &output[1..]),
        _ => return Err(Error::new("HOST_TRANSPORT", "invalid publication marker")),
    };
    if state.is_some_and(|state| state.len() as u64 > limits.state) {
        return Err(Error::new(
            "HOST_TRANSPORT",
            "proposed state exceeds logical limit",
        ));
    }
    let (response_body, trailing) = split(response)?;
    if !trailing.is_empty() || response_body.len() as u64 > limits.response {
        return Err(Error::new("HOST_TRANSPORT", "invalid proposed response"));
    }
    let response = response.to_vec();
    Ok(match state {
        Some(state) => Decision::Commit {
            state: state.to_vec(),
            response,
        },
        None => Decision::Keep { response },
    })
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
    directory: Temporary,
    stage: PathBuf,
    source: PathBuf,
    kernel: PathBuf,
    authenticate: Program,
    control: Program,
    registry: Vec<u8>,
    // Only exact-code replies successfully returned by the checked controller.
    error_replies: HashMap<String, Vec<u8>>,
    limits: Limits,
    published: Published,
    inspector: Option<UnixStream>,
    inspection_sequence: u64,
    prepared: HashMap<String, PreparedProgram>,
    threads: usize,
    timing: Option<Arc<Timing>>,
    storage: Option<storage::Storage>,
    environment: String,
    gpu_mib: usize,
}

struct PreparedProgram {
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

impl Database {
    fn initialize(options: Options) -> Result<Self> {
        let mut storage = options
            .storage
            .as_ref()
            .map(|(path, mode)| storage::Storage::begin(path, *mode))
            .transpose()?;
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
            .map(|path| Timing::open(path).map(Arc::new))
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
        let report = json_helper(&options.root.join("tools/service/stage.mjs"), &arguments)?;
        let programs = report
            .get("programs")
            .ok_or_else(|| Error::new("HOST_JSON", "missing programs"))?;
        let limits = Limits::read(&report)?;
        let initial = Program::load(
            text(programs, if recovering { "recover" } else { "initialize" })?.into(),
            0,
        )?;
        let authenticate = Program::load(text(programs, "authenticate")?.into(), 0)?;
        let control = Program::load(text(programs, "control")?.into(), 0)?;
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
        let environment: Value =
            serde_json::from_slice(&fs::read(directory.path.join("environment.json"))?)?;
        let environment = text(&environment, "identity")?.to_owned();
        if let Some(storage) = &mut storage {
            storage.bind_environment(&fs::read(directory.path.join("environment.bytes"))?)?;
        }
        let state = if recovering {
            storage
                .as_ref()
                .expect("recovery storage")
                .recover(&environment, &limits)?
        } else {
            output[1..].to_vec()
        };
        let inspection_seed = if inspector.is_some() && !recovering {
            Some(fs::read_to_string(
                directory.path.join("initialize/Seed.bend"),
            )?)
        } else {
            None
        };
        fs::remove_dir_all(
            directory
                .path
                .join(if recovering { "recover" } else { "initialize" }),
        )?;
        // Certified initialization and all worker cleanup precede the first
        // durable image. Failed creates leave a directory requiring inspection.
        if !recovering && let Some(storage) = &mut storage {
            storage.persist(&environment, &limits, &state)?;
        }
        let mut database = Self {
            directory,
            stage: text(&report, "stagePath")?.into(),
            source: options.source,
            kernel: options.kernel,
            authenticate,
            control,
            registry: Vec::new(),
            error_replies: HashMap::new(),
            limits,
            published: Published {
                state,
                response: Vec::new(),
            },
            inspector,
            inspection_sequence: 0,
            prepared: HashMap::new(),
            threads: options.threads,
            timing,
            storage,
            environment,
            gpu_mib: options.gpu_mib,
        };
        // HostErrorReplyTheorem states exact output independent of root, last
        // response and registry. Limits stay immutable. Prefill each prepared
        // code separately so these denials work with the controller offline.
        for code in ["HANDLE", "PREPARED_INTEGRITY"] {
            database.checked_error(code)?;
        }
        if database.inspector.is_some() {
            let environment: Value = serde_json::from_slice(&fs::read(
                database.directory.path.join("environment.json"),
            )?)?;
            let mut sources = serde_json::Map::new();
            for entry in fs::read_dir(database.directory.path.join("public"))? {
                let entry = entry?;
                if entry.file_type()?.is_file() {
                    sources.insert(
                        entry.file_name().to_string_lossy().into_owned(),
                        Value::String(fs::read_to_string(entry.path())?),
                    );
                }
            }
            database.inspect(serde_json::json!({
                "event": "initialized", "recovered": recovering, "environment": environment, "sources": sources,
                "seed": inspection_seed,
                "limits": {"message": database.limits.message,
                    "state": database.limits.state, "response": database.limits.response}
            }));
        }
        Ok(database)
    }

    fn inspect(&mut self, metadata: Value) {
        inspect_snapshot(
            &mut self.inspector,
            self.inspection_sequence,
            &self.published.state,
            metadata,
        );
    }

    // Reusable service boundary: input is a complete checked proposal after
    // worker cleanup. Ok is result-ready; Err is fatal (no response or dispatch).
    // Scheduling/timing can wrap this method without moving the durable point.
    fn publish(&mut self, proposal: Result<Decision>) -> Result<Vec<u8>> {
        self.publish_with_ready(proposal, || {})
    }

    // Timing records its endpoint here; final inspector/log/client delivery is
    // outside the measured interval. The callback only records readiness and
    // cannot turn an already committed result into an ordinary failure.
    fn publish_with_ready(
        &mut self,
        mut proposal: Result<Decision>,
        result_ready: impl FnOnce(),
    ) -> Result<Vec<u8>> {
        let mut bench = bench_start();
        // The current state is already durable after create/recovery and every
        // accepted publication. Environment and limits are immutable; state is
        // the image's only varying field. Equal bytes need no new durable image.
        // Still publish Commit's exact response below, even when it differs.
        if let Ok(Decision::Commit { state, .. }) = &proposal
            && state != &self.published.state
            && let Some(storage) = &mut self.storage
        {
            if let Err(error) = storage.persist(&self.environment, &self.limits, state) {
                if error.uncertain {
                    return Err(error.into());
                }
                proposal = Err(error.into());
            } else {
                // Test hook only. Once directory sync succeeds, even a failure
                // before RAM publication must stop without a rollback response.
                storage::fault_point("before_publish")
                    .map_err(|e| Error::new("STORAGE_UNCERTAIN", e.to_string()))?;
            }
        }
        let error_metadata = proposal
            .as_ref()
            .err()
            .map(|error| serde_json::json!({"code": error.code, "message": error.message}));
        let decision = match proposal {
            Ok(decision) => decision,
            Err(error) => {
                diagnostic(format_args!("{}: {}", error.code, error.message));
                let response = self.checked_error(&error.code).unwrap_or_else(|failure| {
                    diagnostic(format_args!(
                        "denial controller failed for {}: {}: {}; using technical failure fallback (not memoized)",
                        error.code, failure.code, failure.message
                    ));
                    error_frame("failure")
                });
                Decision::Keep { response }
            }
        };
        let response = self.published.finish(decision);
        bench_mark(&mut bench, "publication");
        result_ready();
        storage::fault_point("after_publish")
            .map_err(|e| Error::new("STORAGE_UNCERTAIN", e.to_string()))?;
        advance_inspection_sequence(&mut self.inspection_sequence);
        self.inspect(serde_json::json!({"event": "completed", "diagnostic": error_metadata}));
        Ok(response)
    }

    fn preprocess(&self, program: &Program, input: &[u8]) -> Result<Vec<u8>> {
        let output = program.run(input, self.threads)?;
        if !matches!(output.first(), Some(0 | 1 | 3..=5)) {
            return Err(Error::new("HOST_TRANSPORT", "invalid preprocessing result"));
        }
        Ok(output)
    }

    fn propose(&mut self, body: &[u8], attempt: &mut Option<Attempt>) -> Result<Decision> {
        let mut bench = bench_start();
        let input = packet(&self.published.state, body);
        // Input.analyze decodes before authenticating and preserves decode
        // errors. A separate decode child would repeat that entire pass.
        // The worker decodes this same packet and enters through Gate.begin.
        let authenticated = self.preprocess(&self.authenticate, &input)?;
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
        if matches!(operation, 4 | 5) {
            let handle =
                std::str::from_utf8(code).map_err(|_| Error::new("HANDLE", "invalid handle"))?;
            if operation == 5 {
                return self.control_operation(body, "", &[], &[]);
            }
            let prepared = self
                .prepared
                .get(handle)
                .ok_or_else(|| Error::new("HANDLE", "unknown or invalidated handle"))?;
            prepared.validate()?;
            bench_mark(&mut bench, "prepared_integrity");
            if self.inspector.is_some() {
                self.inspect(serde_json::json!({
                    "event": "prepared-resolved", "handle": handle,
                    "original_code": String::from_utf8_lossy(&prepared.original_code),
                    "universal_proof": String::from_utf8_lossy(&prepared.universal_proof)
                }));
            }
            let prepared = &self.prepared[handle];
            // The map locates the artifact; only checked registry lookup authorizes
            // execution. Bend also binds the selected source/proof to this artifact.
            let output = prepared
                .program
                .run(&packet(&self.registry, &input), self.threads)?;
            if prepared.program.gpu.is_some() {
                // CUDA only: the sealed bundle must be unchanged after the run.
                prepared.validate()?;
            }
            bench_mark(&mut bench, "prepared_worker");
            return parse_decision(&output, &self.limits);
        }
        if self.inspector.is_some() {
            self.inspect(serde_json::json!({
                "event": "authenticated",
                "generated_sources": {
                    "Instance.bend": String::from_utf8_lossy(instance),
                    "Bindings.bend": String::from_utf8_lossy(bindings)
                }
            }));
        }
        let mut request = Temporary::new(&self.directory.path, "request")?;
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
                "prepare".into()
            } else {
                "execute".into()
            },
            self.directory.path.clone().into_os_string(),
            request.path.clone().into_os_string(),
            metadata.into_os_string(),
            self.source.clone().into_os_string(),
            self.kernel.clone().into_os_string(),
        ];
        // The CPU default keeps main's exact staging arguments.
        if self.gpu_mib != 0 {
            arguments.push(self.gpu_mib.to_string().into());
        }
        let report = json_helper(&self.stage, &arguments)?;
        if Limits::read(&report)? != self.limits {
            return Err(Error::new(
                "HOST_TRANSPORT",
                "request configuration changed",
            ));
        }
        let program = Program::load(text(&report, "program")?.into(), self.gpu_mib)?;
        bench_mark(&mut bench, "admission_total");
        if operation == 3 {
            let control = self.run_control(body, text(&report, "certificateMode")?, code, proof)?;
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
            sealed.extend(PreparedProgram::seal(&self.directory.path.join("public"))?);
            sealed.extend(PreparedProgram::seal(&self.directory.path.join("runtime"))?);
            self.prepared.insert(
                handle,
                PreparedProgram {
                    directory: request,
                    program,
                    original_code: code.to_vec(),
                    universal_proof: proof.to_vec(),
                    sealed,
                },
            );
            self.registry = registry;
            return Ok(Decision::Keep { response });
        }
        let output = program.run(&input, self.threads)?;
        bench_mark(&mut bench, "ordinary_worker");
        let proposal = parse_decision(&output, &self.limits)?;
        request.remove()?;
        bench_mark(&mut bench, "proposal_cleanup");
        Ok(proposal)
    }

    fn checked_error(&mut self, code: &str) -> Result<Vec<u8>> {
        if let Some(response) = self.error_replies.get(code) {
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
            &packet(&self.registry, &packet(&self.published.state, &[])),
        );
        let output = self.control.run(&input, self.threads)?;
        if output.first() != Some(&0) {
            return Err(Error::new(
                "HOST_TRANSPORT",
                "invalid checked denial result",
            ));
        }
        match parse_decision(&output, &self.limits)? {
            Decision::Keep { response } => {
                self.error_replies.insert(code.to_owned(), response.clone());
                Ok(response)
            }
            Decision::Commit { .. } => unreachable!("denial tag checked above"),
        }
    }

    fn run_control(
        &self,
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
            &packet(&self.registry, &packet(&self.published.state, body)),
        );
        let output = self.control.run(&input, self.threads)?;
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

    fn control_operation(
        &mut self,
        body: &[u8],
        mode: &str,
        code: &[u8],
        proof: &[u8],
    ) -> Result<Decision> {
        match self.run_control(body, mode, code, proof)? {
            ControlDecision::Denied(response) => Ok(Decision::Keep { response }),
            ControlDecision::Remove {
                handle,
                registry,
                response,
            } => {
                // Install the checked removal before artifact cleanup: a cleanup
                // failure must never restore execution authority.
                self.registry = registry;
                match self.prepared.remove(&handle) {
                    Some(mut artifact) => {
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

    fn serve(&mut self) -> Result<()> {
        serve_serial(
            PollInput(io::stdin()),
            &mut io::stdout().lock(),
            self.limits.message,
            |body| self.request(body),
        )
    }
}

// Administrator diagnostics use a modulo-2^64 counter. Semantic run/world/time
// indices in the proofs are independent of this finite display identifier.
fn advance_inspection_sequence(sequence: &mut u64) {
    *sequence = sequence.wrapping_add(1);
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

impl Database {
    // One complete request, including cleanup, durable publication and timing.
    fn request(&mut self, body: &[u8]) -> Result<Vec<u8>> {
        let mut attempt = self.timing.as_ref().map(|timing| timing.selected());
        let proposal = self.propose(body, &mut attempt);
        if self.timing.is_none() {
            return self.publish(proposal);
        }
        let timing = self.timing.clone();
        let response = self.publish_with_ready(proposal, || {
            if let (Some(timing), Some(attempt)) = (&timing, attempt.take()) {
                timing.completed(attempt);
            }
        });
        // Fatal uncertainty can return before result-ready. Record the finished
        // service once, without implying acknowledgment or rollback.
        if let (Some(timing), Some(attempt)) = (&timing, attempt) {
            timing.completed(attempt);
        }
        response
    }
}

fn serve_serial(
    input: impl FrameInput,
    output: &mut impl Write,
    limit: u64,
    request: impl FnMut(&[u8]) -> Result<Vec<u8>>,
) -> Result<()> {
    let mut queue = FrameQueue::start(input, limit, QueueBounds::for_message_limit(limit))?;
    let result = scheduling::coordinate(&queue, output, request, error_frame);
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
    value
        .to_str()
        .filter(|text| !text.is_empty() && text.bytes().all(|byte| byte.is_ascii_digit()))
        .and_then(|text| text.parse::<usize>().ok())
        .filter(|count| (1..=MAX_THREADS).contains(count))
        .ok_or_else(|| Error::new("ARGUMENT", "--threads must be an integer from 1 to 128"))
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
        let mut threads = default_threads();
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
                    "Usage: jaydb2 --configuration FILE [--seed FILE] [--storage DIRECTORY --storage-mode create|open] [--threads N] [--gpu off|MiB] [--bend-source DIR] [--bendtt FILE] [--inspect-socket ADMIN_SOCKET] [--timing-log FILE|-]\n\n--seed FILE  Required for volatile mode and storage create; forbidden for storage open\n--storage DIRECTORY --storage-mode create|open  Opt-in complete-image persistence; create requires a new directory, open requires its authoritative snapshot and the exact same environment/executable\n--timing-log FILE|-  Administrator elapsed-service NDJSON, - selects stderr\n--threads N  Native CPU workers per process, 1 to 128 (default: available CPU parallelism, capped at 128)\n--gpu off|MiB  Official CUDA for ! calls, 64..4096 MiB (default: off); executions stay serial"
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
                Some("--inspect-socket") => inspect_socket = Some(PathBuf::from(value)),
                Some("--timing-log") => timing_log = Some(PathBuf::from(value)),
                Some("--threads") => threads = parse_threads(&value)?,
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
            Database::initialize(options)?.serve()?;
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
        serve_serial(input, output, limit, request)
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
    fn only_a_complete_valid_proposal_replaces_the_published_pair() {
        let limits = Limits {
            message: 100,
            state: 3,
            response: error_frame("success").len() as u64 - 8,
        };
        let mut published = Published {
            state: b"old".to_vec(),
            response: Vec::new(),
        };
        let success = [vec![1], packet(b"new", &error_frame("success"))].concat();
        assert_eq!(
            published.finish(parse_decision(&success, &limits).unwrap()),
            error_frame("success")
        );
        let refusal = [vec![0], error_frame("refusal")].concat();
        assert_eq!(
            published.finish(parse_decision(&refusal, &limits).unwrap()),
            error_frame("refusal")
        );
        for invalid in [
            vec![],
            vec![2],
            vec![1, 0],
            [vec![0], error_frame("certificate")].concat(),
            [vec![1], packet(b"long", &error_frame("success"))].concat(),
            [vec![1], packet(b"new", &error_frame("certificate"))].concat(),
            [vec![1], packet(b"new", b"unframed")].concat(),
            [
                vec![1],
                packet(b"new", &[error_frame("success"), vec![0]].concat()),
            ]
            .concat(),
        ] {
            assert!(parse_decision(&invalid, &limits).is_err());
            assert_eq!(published.state, b"new");
            assert_eq!(published.response, error_frame("success"));
        }
        assert_eq!(published.state, b"new");
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
        let mut published = Published {
            state: b"old".to_vec(),
            response: Vec::new(),
        };
        let result = serve_stream(
            Cursor::new(packet(b"call", &[])),
            &mut BrokenOutput,
            4,
            |_| {
                Ok(published.finish(Decision::Commit {
                    state: b"new".to_vec(),
                    response: error_frame("success"),
                }))
            },
        );
        assert!(result.is_err());
        assert_eq!(published.state, b"new");
        assert_eq!(published.response, error_frame("success"));
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
    fn result_ready_follows_commit_and_precedes_final_inspector_output() {
        let directory = Temporary::new(&std::env::temp_dir(), "jaydb-ready").unwrap();
        let path = directory.path.join("db");
        let limits = Limits {
            message: 100,
            state: 10,
            response: 100,
        };
        let environment = "a".repeat(64);
        let mut storage = storage::Storage::begin(&path, storage::Mode::Create).unwrap();
        storage
            .bind_environment(b"publication test environment")
            .unwrap();
        storage.persist(&environment, &limits, b"old").unwrap();
        let previous = fs::read(path.join("snapshot")).unwrap();
        let (inspector, mut observer) = UnixStream::pair().unwrap();
        observer.set_nonblocking(true).unwrap();
        let mut db = Database {
            directory,
            stage: PathBuf::new(),
            source: PathBuf::new(),
            kernel: PathBuf::new(),
            authenticate: Program {
                path: PathBuf::new(),
                sha256: String::new(),
                gpu: None,
            },
            limits,
            published: Published {
                state: b"old".to_vec(),
                response: Vec::new(),
            },
            inspector: Some(inspector),
            inspection_sequence: u64::MAX,
            prepared: HashMap::new(),
            control: Program {
                path: PathBuf::new(),
                sha256: String::new(),
                gpu: None,
            },
            registry: Vec::new(),
            error_replies: HashMap::new(),
            threads: 1,
            timing: None,
            storage: Some(storage),
            environment,
            gpu_mib: 0,
        };
        // Equal state with a different response still publishes the pair, but
        // must not replace the durable inode. Keep it open to prevent inode reuse.
        use std::os::unix::fs::MetadataExt;
        let durable = fs::File::open(path.join("snapshot")).unwrap();
        let inode = durable.metadata().unwrap().ino();
        let first_response = error_frame("first-success");
        assert_eq!(
            db.publish(Ok(Decision::Commit {
                state: b"old".to_vec(),
                response: first_response.clone(),
            }))
            .unwrap(),
            first_response
        );
        assert_eq!(db.published.response, first_response);
        assert_eq!(db.published.state, b"old");
        assert_eq!(fs::metadata(path.join("snapshot")).unwrap().ino(), inode);
        assert_eq!(fs::read(path.join("snapshot")).unwrap(), previous);
        // Drain this completion's inspection event before checking readiness.
        assert!(observer.read(&mut [0; 1024]).unwrap() > 0);
        db.inspection_sequence = u64::MAX;
        let mut notified = false;
        let response = error_frame("success");
        assert_eq!(
            db.publish_with_ready(
                Ok(Decision::Commit {
                    state: b"new".to_vec(),
                    response: response.clone()
                }),
                || {
                    notified = true;
                    assert_ne!(fs::read(path.join("snapshot")).unwrap(), previous);
                    let mut byte = [0];
                    assert_eq!(
                        observer.read(&mut byte).unwrap_err().kind(),
                        io::ErrorKind::WouldBlock
                    );
                }
            )
            .unwrap(),
            response
        );
        assert!(notified);
        assert_eq!(db.published.state, b"new");
        assert_eq!(db.inspection_sequence, 0);
        assert_eq!(
            db.storage
                .as_ref()
                .unwrap()
                .recover(&db.environment, &db.limits)
                .unwrap(),
            b"new"
        );
        assert!(observer.read(&mut [0; 1024]).unwrap() > 0);

        // The host must forward the controller's bytes, even when a test
        // executable returns a different status from the old Rust table.
        use std::os::unix::fs::PermissionsExt;
        let executable = db.directory.path.join("denial");
        let script = b"#!/bin/sh\ncat > \"$0.input\"\ncat \"$0.reply\"\n";
        fs::write(&executable, script).unwrap();
        fs::set_permissions(&executable, fs::Permissions::from_mode(0o700)).unwrap();
        db.control = Program {
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
                db.publish(Err(Error::new(code, "test failure"))).unwrap(),
                forwarded
            );
            assert_eq!(db.published.state, b"new");
            assert_eq!(db.published.response, response);
            let input = fs::read(executable.with_extension("input")).unwrap();
            let (metadata, rest) = split(&input).unwrap();
            let mut expected = vec![4];
            expected.extend_from_slice(&(code.len() as u64).to_be_bytes());
            expected.extend_from_slice(code.as_bytes());
            assert_eq!(metadata, expected);
            let (registry, rest) = split(rest).unwrap();
            assert_eq!(registry, db.registry);
            let (root, body) = split(rest).unwrap();
            assert_eq!(root, b"new");
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
            db.publish(Err(Error::new("HOST_IO", "rejected"))).unwrap(),
            error_frame("failure")
        );
        assert_eq!(db.published.state, b"new");
        assert_eq!(db.published.response, response);
        assert!(observer.read(&mut [0; 1024]).unwrap() > 0);
        assert!(!db.error_replies.contains_key("HOST_IO"));
        // A later successful exact-code reply must replace neither a prepared
        // entry nor a fallback; only this checked reply is memoized.
        let host_io_reply = error_frame("host-io-specific");
        fs::write(
            executable.with_extension("reply"),
            [vec![0], host_io_reply.clone()].concat(),
        )
        .unwrap();
        assert_eq!(
            db.publish(Err(Error::new("HOST_IO", "retry"))).unwrap(),
            host_io_reply
        );
        let input = fs::read(executable.with_extension("input")).unwrap();
        let (metadata, _) = split(&input).unwrap();
        assert_eq!(metadata, [vec![4], packet(b"HOST_IO", &[])].concat());
        assert!(observer.read(&mut [0; 1024]).unwrap() > 0);
        fs::remove_file(&executable).unwrap();
        for _ in 0..2 {
            assert_eq!(
                db.publish(Err(Error::new("UNSEEN_CODE", "rejected")))
                    .unwrap(),
                error_frame("failure")
            );
            assert_eq!(db.published.state, b"new");
            assert_eq!(db.published.response, response);
            assert!(observer.read(&mut [0; 1024]).unwrap() > 0);
            assert!(!db.error_replies.contains_key("UNSEEN_CODE"));
        }
        assert_eq!(
            db.publish(Err(Error::new("HOST_IO", "memoized"))).unwrap(),
            host_io_reply
        );
        assert!(observer.read(&mut [0; 1024]).unwrap() > 0);
        for code in ["PRIMARY_CHECK", "HANDLE", "PREPARED_INTEGRITY"] {
            let error = Error::new(code, "physical prepared failure");
            assert_eq!(db.publish(Err(error)).unwrap(), forwarded);
            assert_eq!(db.published.state, b"new");
            assert_eq!(db.published.response, response);
            assert!(observer.read(&mut [0; 1024]).unwrap() > 0);
        }
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
