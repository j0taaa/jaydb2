//! Serial host. Official Bend workers own computation; this process owns publication.
mod scheduling;
mod service_policy;

use scheduling::{FrameInput, FrameQueue, PollInput, QueueBounds, SerialService};
use serde_json::Value;
use service_policy::{Attempt, Monotonic, Quota, ServicePolicy};
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::ffi::{OsStr, OsString};
use std::fs::{self, DirBuilder, File, OpenOptions};
use std::io::{self, Read, Write};
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

type Result<T> = std::result::Result<T, Error>;

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

    fn response(&self) -> Vec<u8> {
        if self.code == "CONTROL_LIMIT" {
            return error_frame("limit");
        }
        let refused = [
            "IMPORT",
            "IMPORT_CYCLE",
            "DEPENDENCY",
            "PARSE",
            "META",
            "UNSAFE",
            "FOREIGN",
            "IO",
            "OPEN_LAW",
            "SHADOW",
            "REDEFINITION",
            "PRIMARY_CHECK",
            "BENDTT_CHECK",
            "TARGET",
            "SOURCE_BINDING",
            "HOST_CAPTURE",
            "KERNEL_CAPTURE",
        ];
        error_frame(if refused.contains(&self.code.as_str()) {
            "certificate"
        } else {
            "failure"
        })
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

fn capture(command: &mut Command, input: &[u8]) -> Result<Output> {
    let mut child = command
        .env("BEND_NO_TELEMETRY", "1")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    let mut stdin = child.stdin.take().expect("piped child stdin");
    let mut stdout = child.stdout.take().expect("piped child stdout");
    let mut stderr = child.stderr.take().expect("piped child stderr");
    // Drain stdout/stderr while sending input, only binary pipes cannot deadlock
    // when a worker rejects input before reading its complete body.
    std::thread::scope(|scope| {
        let writer = scope.spawn(move || stdin.write_all(input));
        let reader = scope.spawn(move || {
            let mut bytes = Vec::new();
            stdout.read_to_end(&mut bytes).map(|_| bytes)
        });
        let errors = scope.spawn(move || {
            let mut bytes = Vec::new();
            stderr.read_to_end(&mut bytes).map(|_| bytes)
        });
        let waited = child.wait();
        if waited.is_err() {
            let _ = child.kill();
            if let Err(error) = child.wait() {
                // An unreaped helper cannot become a normal request failure.
                eprintln!("jaydb2: cannot reap helper: {error}");
                std::process::abort();
            }
        }
        let status = waited?;
        let written = writer
            .join()
            .map_err(|_| Error::new("HOST_PIPE", "input writer failed"))?;
        let stdout = reader
            .join()
            .map_err(|_| Error::new("HOST_PIPE", "output reader failed"))??;
        let stderr = errors
            .join()
            .map_err(|_| Error::new("HOST_PIPE", "error reader failed"))??;
        if status.success() {
            written?;
        }
        Ok(Output {
            status,
            stdout,
            stderr,
        })
    })
}

fn json_helper(script: &Path, arguments: &[OsString]) -> Result<Value> {
    let output = capture(
        Command::new("node")
            .arg("--stack_size=65536")
            .arg(script)
            .args(arguments),
        &[],
    )?;
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
}

impl Program {
    fn load(path: PathBuf) -> Result<Self> {
        let report: Value = serde_json::from_slice(&fs::read(format!("{}.json", path.display()))?)?;
        if text(&report, "format")? != "jaydb-official-c-v1" {
            return Err(Error::new(
                "HOST_NATIVE",
                "invalid official executable manifest",
            ));
        }
        let program = Self {
            path,
            sha256: text(&report, "executableSha256")?.into(),
        };
        program.validate()?;
        Ok(program)
    }

    fn validate(&self) -> Result<()> {
        let actual = format!("{:x}", Sha256::digest(fs::read(&self.path)?));
        if actual != self.sha256 {
            return Err(Error::new(
                "HOST_NATIVE",
                "official executable hash mismatch",
            ));
        }
        Ok(())
    }

    fn run(&self, input: &[u8], threads: usize) -> Result<Vec<u8>> {
        self.validate()?;
        let output = capture(
            Command::new(&self.path)
                .args(["+RTS", "--threads"])
                .arg(threads.to_string())
                .args(["--gpu", "off", "-RTS"]),
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

struct Published {
    state: Vec<u8>,
    response: Vec<u8>,
}

impl Published {
    fn finish(&mut self, proposal: Result<(Vec<u8>, Option<Vec<u8>>)>) -> Vec<u8> {
        match proposal {
            Ok((response, Some(state))) => {
                // Both values and all cleanup are complete before this store.
                *self = Self { state, response };
                self.response.clone()
            }
            Ok((response, None)) => response,
            Err(error) => {
                eprintln!("jaydb2: {}: {}", error.code, error.message);
                error.response()
            }
        }
    }
}

fn checked_proposal(output: &[u8], limits: &Limits) -> Result<(Vec<u8>, Option<Vec<u8>>)> {
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
    Ok((response.to_vec(), state.map(|state| state.to_vec())))
}

struct Database {
    directory: Temporary,
    stage: PathBuf,
    source: PathBuf,
    kernel: PathBuf,
    authenticate: Program,
    limits: Limits,
    published: Published,
    inspector: Option<UnixStream>,
    inspection_sequence: u64,
    prepared: HashMap<String, PreparedProgram>,
    threads: usize,
    service_policy: Option<ServicePolicy<Monotonic>>,
    timing_log: Option<TimingLog>,
}

// Administrator output only, never inherited by workers or written to stdout.
enum TimingLog {
    Stderr,
    File(File),
}

impl TimingLog {
    fn open(path: &Path) -> Result<Self> {
        if path == Path::new("-") {
            Ok(Self::Stderr)
        } else {
            Ok(Self::File(
                OpenOptions::new()
                    .create(true)
                    .append(true)
                    .mode(0o600)
                    .open(path)?,
            ))
        }
    }

    fn write(&mut self, receipt: &Value) -> io::Result<()> {
        let mut line = serde_json::to_vec(receipt)?;
        line.push(b'\n');
        match self {
            Self::Stderr => io::stderr().lock().write_all(&line),
            Self::File(file) => file.write_all(&line),
        }
    }
}

struct PreparedProgram {
    directory: Temporary,
    program: Program,
    original_code: Vec<u8>,
    universal_proof: Vec<u8>,
    // Host-owned snapshots; checking these bytes does not invoke admission.
    sealed: Vec<(PathBuf, String)>,
}

impl PreparedProgram {
    fn seal(directory: &Path) -> Result<Vec<(PathBuf, String)>> {
        let mut files = Vec::new();
        for entry in fs::read_dir(directory)? {
            let entry = entry?;
            if entry.file_type()?.is_dir() {
                files.extend(Self::seal(&entry.path())?);
            } else if entry.file_type()?.is_file() {
                files.push((
                    entry.path(),
                    format!("{:x}", Sha256::digest(fs::read(entry.path())?)),
                ));
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
            if !metadata.file_type().is_file()
                || format!("{:x}", Sha256::digest(fs::read(path)?)) != *expected
            {
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
        let timing_log = options
            .timing_log
            .as_deref()
            .map(TimingLog::open)
            .transpose()?;
        let directory = Temporary::new(&std::env::temp_dir(), "jaydb2")?;
        let report = json_helper(
            &options.root.join("tools/service/stage.mjs"),
            &[
                "initialize".into(),
                directory.path.clone().into_os_string(),
                options.configuration.into_os_string(),
                options.seed.into_os_string(),
                options.source.clone().into_os_string(),
                options.kernel.clone().into_os_string(),
            ],
        )?;
        let programs = report
            .get("programs")
            .ok_or_else(|| Error::new("HOST_JSON", "missing programs"))?;
        let limits = Limits::read(&report)?;
        let initial = Program::load(text(programs, "initialize")?.into())?;
        let authenticate = Program::load(text(programs, "authenticate")?.into())?;
        let output = initial.run(&[], options.threads)?;
        if output.first() != Some(&1) || output.len() as u64 - 1 > limits.state {
            return Err(Error::new(
                "CONFIGURATION",
                "invalid configuration or initial state",
            ));
        }
        let inspection_seed = if inspector.is_some() {
            Some(fs::read_to_string(
                directory.path.join("initialize/Seed.bend"),
            )?)
        } else {
            None
        };
        fs::remove_dir_all(directory.path.join("initialize"))?;
        let mut database = Self {
            directory,
            stage: text(&report, "stagePath")?.into(),
            source: options.source,
            kernel: options.kernel,
            authenticate,
            limits,
            published: Published {
                state: output[1..].to_vec(),
                response: Vec::new(),
            },
            inspector,
            inspection_sequence: 0,
            prepared: HashMap::new(),
            threads: options.threads,
            service_policy: if timing_log.is_some() || options.quota.is_some() {
                Some(ServicePolicy::new(Monotonic::new(), options.quota))
            } else {
                None
            },
            timing_log,
        };
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
                "event": "initialized", "environment": environment, "sources": sources,
                "seed": inspection_seed,
                "limits": {"message": database.limits.message,
                    "state": database.limits.state, "response": database.limits.response}
            }));
        }
        Ok(database)
    }

    fn inspect(&mut self, mut metadata: Value) {
        if let Some(stream) = &mut self.inspector {
            metadata["sequence"] = self.inspection_sequence.into();
            // Preserve the exact canonical state bytes already owned by the
            // host; the inspector does not compute or publish another state.
            let result = (|| -> io::Result<()> {
                let encoded = serde_json::to_vec(&metadata)?;
                stream.write_all(&packet(&encoded, &[]))?;
                stream.write_all(&packet(&self.published.state, &[]))?;
                stream.flush()
            })();
            if let Err(error) = result {
                eprintln!("jaydb2: INSPECTOR: {error}");
                self.inspector = None;
            }
        }
    }

    fn publish_completed(&mut self, completion: ServiceCompletion) -> Vec<u8> {
        let ServiceCompletion { proposal, attempt } = completion;
        let diagnostic = proposal
            .as_ref()
            .err()
            .map(|error| serde_json::json!({"code": error.code, "message": error.message}));
        let response = self.published.finish(proposal);
        // A persistence adapter must commit durably before this completion hook.
        // Publication, worker reaping, and all request temporary cleanup precede it.
        self.inspection_sequence += 1;
        if let (Some(policy), Some(attempt)) = (&mut self.service_policy, attempt) {
            let mut receipt = policy.completed(attempt);
            receipt["sequence"] = self.inspection_sequence.into();
            if let Some(log) = &mut self.timing_log
                && let Err(error) = log.write(&receipt)
            {
                eprintln!("jaydb2: TIMING_LOG: {error}");
                self.timing_log = None;
            }
        }
        self.inspect(serde_json::json!({"event": "completed", "diagnostic": diagnostic}));
        response
    }

    fn preprocess(&self, program: &Program, input: &[u8]) -> Result<Vec<u8>> {
        let output = program.run(input, self.threads)?;
        if !matches!(output.first(), Some(0 | 1)) {
            return Err(Error::new("HOST_TRANSPORT", "invalid preprocessing result"));
        }
        Ok(output)
    }

    fn propose(
        &mut self,
        body: &[u8],
        attempt: &mut Option<Attempt>,
    ) -> Result<(Vec<u8>, Option<Vec<u8>>)> {
        // 7 is outside the canonical Value tags (0..6). The extension contains
        // one opcode and an otherwise ordinary, officially decoded request.
        let (operation, body) = if body.first() == Some(&7) {
            match body.get(1) {
                Some(op @ 0..=2) => (Some(*op), &body[2..]),
                _ => return Ok((error_frame("input"), None)),
            }
        } else {
            (None, body)
        };
        let input = packet(&self.published.state, body);
        // Input.analyze decodes before authenticating and preserves decode
        // errors. A separate decode child would repeat that entire pass.
        // Execution still analyzes this same packet in its own fresh process.
        let authenticated = self.preprocess(&self.authenticate, &input)?;
        if authenticated[0] == 0 {
            return Ok((authenticated[1..].to_vec(), None));
        }
        // Private worker bytes: length-prefixed exact Context.id, then the
        // prior metadata. Never parse identity out of generated Bend source.
        let (principal, metadata) = split(&authenticated[1..])?;
        let principal = std::str::from_utf8(principal)
            .map_err(|_| Error::new("HOST_TRANSPORT", "invalid authenticated principal"))?;
        if let (Some(policy), Some(attempt)) = (&mut self.service_policy, attempt)
            && !policy.authenticated(attempt, principal)
        {
            // Opt-in host receipt outside S.Status, still bounded by the
            // response ceiling. It is shorter than the required fixed
            // certificate error. No admission, registry mutation, or start.
            return self.control_response("quota", None);
        }
        let (code, rest) = split(metadata)?;
        let (proof, rest) = split(rest)?;
        let (instance, bindings) = split(rest)?;
        if matches!(operation, Some(1 | 2)) {
            if !proof.is_empty() {
                return Ok((error_frame("input"), None));
            }
            let handle =
                std::str::from_utf8(code).map_err(|_| Error::new("HANDLE", "invalid handle"))?;
            if operation == Some(2) {
                if !self.prepared.contains_key(handle) {
                    return Err(Error::new("HANDLE", "unknown or invalidated handle"));
                }
                let response = self.control_response("invalidated", None)?;
                let mut prepared = self.prepared.remove(handle).expect("serial handle lookup");
                prepared.directory.remove()?;
                return Ok(response);
            }
            let prepared = self
                .prepared
                .get(handle)
                .ok_or_else(|| Error::new("HANDLE", "unknown or invalidated handle"))?;
            prepared.validate()?;
            if self.inspector.is_some() {
                self.inspect(serde_json::json!({
                    "event": "prepared-resolved", "handle": handle,
                    "original_code": String::from_utf8_lossy(&prepared.original_code),
                    "universal_proof": String::from_utf8_lossy(&prepared.universal_proof)
                }));
            }
            let prepared = &self.prepared[handle];
            // Only the native executable runs here. Its ordinary Input.analyze
            // authenticates the received credential again on this same state;
            // E.start receives that context and the actual decoded arguments.
            return checked_proposal(&prepared.program.run(&input, self.threads)?, &self.limits);
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
        let report = json_helper(
            &self.stage,
            &[
                if operation == Some(0) {
                    "prepare".into()
                } else {
                    "execute".into()
                },
                self.directory.path.clone().into_os_string(),
                request.path.clone().into_os_string(),
                metadata.into_os_string(),
                self.source.clone().into_os_string(),
                self.kernel.clone().into_os_string(),
            ],
        )?;
        if Limits::read(&report)? != self.limits {
            return Err(Error::new(
                "HOST_TRANSPORT",
                "request configuration changed",
            ));
        }
        let program = Program::load(text(&report, "program")?.into())?;
        if operation == Some(0) {
            if text(&report, "certificateMode")? != "universal" {
                return Err(Error::new(
                    "TARGET",
                    "preparation requires a universal certificate",
                ));
            }
            let handle = loop {
                let mut random = [0u8; 32];
                fs::File::open("/dev/urandom")?.read_exact(&mut random)?;
                let candidate: String = random.iter().map(|byte| format!("{byte:02x}")).collect();
                if !self.prepared.contains_key(&candidate) {
                    break candidate;
                }
            };
            let response = self.control_response("prepared", Some(&handle))?;
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
            return Ok(response);
        }
        let output = program.run(&input, self.threads)?;
        let proposal = checked_proposal(&output, &self.limits)?;
        request.remove()?;
        Ok(proposal)
    }

    fn control_response(
        &self,
        status: &str,
        value: Option<&str>,
    ) -> Result<(Vec<u8>, Option<Vec<u8>>)> {
        let response = response_frame(status, value);
        if (response.len() - 8) as u64 > self.limits.response {
            return Err(Error::new(
                "CONTROL_LIMIT",
                "prepared response exceeds logical limit",
            ));
        }
        Ok((response, None))
    }

    fn serve(&mut self) -> Result<()> {
        serve_serial(
            PollInput(io::stdin()),
            &mut io::stdout().lock(),
            self.limits.message,
            self,
        )
    }
}

struct ServiceCompletion {
    proposal: Result<(Vec<u8>, Option<Vec<u8>>)>,
    attempt: Option<Attempt>,
}

impl SerialService for Database {
    type Completion = ServiceCompletion;

    fn execute(&mut self, body: &[u8]) -> Self::Completion {
        // Only Request dispatch reaches this hook, after queue selection.
        // Frame reception/queue waits and terminal events are not timed.
        let mut attempt = self.service_policy.as_ref().map(ServicePolicy::selected);
        let proposal = self.propose(body, &mut attempt);
        ServiceCompletion { proposal, attempt }
    }

    fn publish(&mut self, completion: Self::Completion) -> Result<Vec<u8>> {
        Ok(self.publish_completed(completion))
    }
}

fn serve_serial(
    input: impl FrameInput,
    output: &mut impl Write,
    limit: u64,
    service: &mut impl SerialService,
) -> Result<()> {
    let mut queue = FrameQueue::start(input, limit, QueueBounds::for_message_limit(limit))?;
    let result = scheduling::coordinate(&queue, output, service, error_frame);
    // This also wakes a reader still waiting on an open stdin or queue capacity.
    let cleanup = queue.close();
    result?;
    cleanup?;
    Ok(())
}

struct Options {
    root: PathBuf,
    configuration: PathBuf,
    seed: PathBuf,
    source: PathBuf,
    kernel: PathBuf,
    inspect_socket: Option<PathBuf>,
    threads: usize,
    timing_log: Option<PathBuf>,
    quota: Option<Quota>,
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

fn parse_milliseconds(value: &OsStr) -> Result<std::time::Duration> {
    value
        .to_str()
        .filter(|text| !text.is_empty() && text.bytes().all(|byte| byte.is_ascii_digit()))
        .and_then(|text| text.parse::<u64>().ok())
        .filter(|value| *value > 0)
        .map(std::time::Duration::from_millis)
        .ok_or_else(|| {
            Error::new(
                "ARGUMENT",
                "quota milliseconds must be a positive uint64 integer",
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
        let mut timing_log = None;
        let mut quota_period = None;
        let mut quota_budget = None;
        let mut source = root.join(format!(".tools/bend-source-{}", text(&lock, "version")?));
        let mut kernel = root.join(format!(".tools/bendtt-{}", text(&lock, "kernelSha256")?));
        let mut arguments = arguments.into_iter();
        while let Some(argument) = arguments.next() {
            if argument == "--help" || argument == "-h" {
                println!(
                    "Usage: jaydb2 --configuration FILE --seed FILE [--threads N] [--bend-source DIR] [--bendtt FILE] [--inspect-socket ADMIN_SOCKET] [--timing-log FILE|-] [--quota-period-ms N --quota-budget-ms N]\n\n--timing-log  Administrator NDJSON service timings; - selects stderr\n--quota-period-ms / --quota-budget-ms  Positive fixed-period soft per-user quota; opt-in quota control receipts\n--threads N  CPU workers per native program, 1 to 128 (default: available CPU parallelism, capped at 128)"
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
                Some("--threads") => threads = parse_threads(&value)?,
                Some("--timing-log") => timing_log = Some(PathBuf::from(value)),
                Some("--quota-period-ms") => quota_period = Some(parse_milliseconds(&value)?),
                Some("--quota-budget-ms") => quota_budget = Some(parse_milliseconds(&value)?),
                _ => {
                    return Err(Error::new(
                        "ARGUMENT",
                        format!("unknown option {}", argument.to_string_lossy()),
                    ));
                }
            }
        }
        let quota = match (quota_period, quota_budget) {
            (None, None) => None,
            (Some(period), Some(budget)) => Some(Quota { period, budget }),
            _ => {
                return Err(Error::new(
                    "ARGUMENT",
                    "--quota-period-ms and --quota-budget-ms must be supplied together",
                ));
            }
        };
        Ok(Some(Self {
            root,
            configuration: fs::canonicalize(
                configuration
                    .ok_or_else(|| Error::new("ARGUMENT", "--configuration is required"))?,
            )?,
            seed: fs::canonicalize(
                seed.ok_or_else(|| Error::new("ARGUMENT", "--seed is required"))?,
            )?,
            source: fs::canonicalize(source)?,
            kernel: fs::canonicalize(kernel)?,
            inspect_socket,
            threads,
            timing_log,
            quota,
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
        eprintln!("jaydb2: {}: {}", error.code, error.message);
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;
    use std::os::unix::fs::PermissionsExt;

    struct TestService<F>(F);

    impl<F: FnMut(&[u8]) -> Vec<u8>> SerialService for TestService<F> {
        type Completion = Vec<u8>;
        fn execute(&mut self, body: &[u8]) -> Vec<u8> {
            (self.0)(body)
        }
        fn publish(&mut self, response: Vec<u8>) -> Result<Vec<u8>> {
            Ok(response)
        }
    }

    fn serve_stream(
        input: impl FrameInput,
        output: &mut impl Write,
        limit: u64,
        request: impl FnMut(&[u8]) -> Vec<u8>,
    ) -> Result<()> {
        serve_serial(input, output, limit, &mut TestService(request))
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
    fn policy_options_are_opt_in_and_require_positive_paired_milliseconds() {
        for value in ["", "0", "-1", "+1", " 1", "1.5", "18446744073709551616"] {
            assert!(parse_milliseconds(OsStr::new(value)).is_err());
        }
        assert_eq!(
            parse_milliseconds(OsStr::new("1")).unwrap(),
            std::time::Duration::from_millis(1)
        );
        assert!(parse_milliseconds(OsStr::new("18446744073709551615")).is_ok());
        assert!(Options::read_from(["--quota-period-ms".into(), "100".into()]).is_err());
        assert!(Options::read_from(["--quota-budget-ms".into(), "10".into()]).is_err());
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let base = vec![
            "--configuration".into(),
            root.join("examples/access/Configuration.bend")
                .into_os_string(),
            "--seed".into(),
            root.join("examples/access/Seed.bend").into_os_string(),
        ];
        let ordinary = Options::read_from(base.clone()).unwrap().unwrap();
        assert!(ordinary.quota.is_none() && ordinary.timing_log.is_none());
        let enabled = Options::read_from(base.into_iter().chain([
            "--quota-period-ms".into(),
            "100".into(),
            "--quota-budget-ms".into(),
            "10".into(),
            "--timing-log".into(),
            "-".into(),
        ]))
        .unwrap()
        .unwrap();
        assert_eq!(
            enabled.quota.unwrap().budget,
            std::time::Duration::from_millis(10)
        );
        assert_eq!(enabled.timing_log.unwrap(), PathBuf::from("-"));
    }

    #[test]
    fn private_auth_principal_is_exact_bytes_and_metadata_is_unchanged() {
        for id in ["", "alice", "α\\\"\n", "alice\0bob"] {
            let metadata = b"unchanged checked code/proof/instance/links";
            let success = packet(id.as_bytes(), metadata);
            let (principal, remaining) = split(&success).unwrap();
            assert_eq!(std::str::from_utf8(principal).unwrap(), id);
            assert_eq!(remaining, metadata);
        }
        assert!(split(&[0; 7]).is_err());
        assert!(split(&9u64.to_be_bytes()).is_err());
        // The host-only receipt deliberately has its own status and no value.
        assert_ne!(error_frame("quota"), error_frame("limit"));
        assert_ne!(error_frame("quota"), error_frame("failure"));
        assert_ne!(error_frame("quota"), error_frame("certificate"));
        assert!(error_frame("quota").len() < error_frame("certificate").len());
        assert_eq!(error_frame("quota").len() - 8, 53);
    }

    #[test]
    fn administrator_timing_log_is_ndjson_and_surfaces_write_errors() {
        let mut directory = Temporary::new(&std::env::temp_dir(), "jaydb-timing-log-test").unwrap();
        let path = directory.path.join("timing.ndjson");
        let mut log = TimingLog::open(&path).unwrap();
        log.write(&serde_json::json!({"principal": "alice\n\"", "elapsed_ns": "42"}))
            .unwrap();
        log.write(&serde_json::json!({"principal": null})).unwrap();
        let bytes = fs::read_to_string(&path).unwrap();
        let lines = bytes
            .lines()
            .map(|line| serde_json::from_str::<Value>(line).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(lines.len(), 2);
        assert_eq!(lines[0]["principal"], "alice\n\"");
        assert_eq!(
            fs::metadata(path).unwrap().permissions().mode() & 0o777,
            0o600
        );
        assert!(
            TimingLog::open(Path::new("/dev/full"))
                .unwrap()
                .write(&Value::Null)
                .is_err()
        );
        directory.remove().unwrap();
    }

    #[test]
    fn native_launch_forwards_selected_cpu_workers_with_gpu_disabled() {
        let directory = Temporary::new(&std::env::temp_dir(), "jaydb-threads-test").unwrap();
        let path = directory.path.join("worker");
        fs::write(&path, "#!/bin/sh\nprintf '%s\\n' \"$@\"\n").unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).unwrap();
        let program = Program {
            sha256: format!("{:x}", Sha256::digest(fs::read(&path).unwrap())),
            path,
        };
        for count in [1, 8, 128] {
            assert_eq!(
                program.run(&[], count).unwrap(),
                format!("+RTS\n--threads\n{count}\n--gpu\noff\n-RTS\n").as_bytes()
            );
        }
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
        assert_eq!(
            Error::new("PRIMARY_CHECK", "proof rejected").response(),
            error_frame("certificate")
        );
        assert_eq!(
            Error::new("NATIVE", "child exited").response(),
            error_frame("failure")
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
            error_frame(if body == b"bad" { "input" } else { "refusal" })
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
            published.finish(checked_proposal(&success, &limits)),
            error_frame("success")
        );
        let refusal = [vec![0], error_frame("refusal")].concat();
        assert_eq!(
            published.finish(checked_proposal(&refusal, &limits)),
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
            assert_eq!(
                published.finish(checked_proposal(&invalid, &limits)),
                error_frame("failure")
            );
            assert_eq!(published.state, b"new");
            assert_eq!(published.response, error_frame("success"));
        }
        assert_eq!(
            published.finish(Err(Error::new("PRIMARY_CHECK", "rejected"))),
            error_frame("certificate")
        );
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
            |_| published.finish(Ok((error_frame("success"), Some(b"new".to_vec())))),
        );
        assert!(result.is_err());
        assert_eq!(published.state, b"new");
        assert_eq!(published.response, error_frame("success"));
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
