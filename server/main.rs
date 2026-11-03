//! Serial host. Official Bend workers own computation; this process owns publication.
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::ffi::OsString;
use std::fs::{self, DirBuilder};
use std::io::{self, Read, Write};
use std::os::unix::fs::DirBuilderExt;
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
            "certificado"
        } else {
            "falha"
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
    // Drain stdout/stderr while sending input, so binary pipes cannot deadlock
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
            message: number("mensagem")?,
            state: number("estado")?,
            response: number("resposta")?,
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

    fn run(&self, input: &[u8]) -> Result<Vec<u8>> {
        self.validate()?;
        let output = capture(
            Command::new(&self.path).args(["+RTS", "--threads", "1", "--gpu", "off", "-RTS"]),
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
    fn string(output: &mut Vec<u8>, value: &str) {
        output.push(4);
        output.extend_from_slice(&(value.len() as u64).to_be_bytes());
        output.extend_from_slice(value.as_bytes());
    }
    let mut body = vec![6];
    body.extend_from_slice(&2u64.to_be_bytes());
    string(&mut body, "status");
    string(&mut body, status);
    string(&mut body, "valor");
    body.push(0);
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
    decode: Program,
    authenticate: Program,
    limits: Limits,
    published: Published,
    inspector: Option<UnixStream>,
    inspection_sequence: u64,
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
        let decode = Program::load(text(programs, "decode")?.into())?;
        let authenticate = Program::load(text(programs, "authenticate")?.into())?;
        let output = initial.run(&[])?;
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
            decode,
            authenticate,
            limits,
            published: Published {
                state: output[1..].to_vec(),
                response: Vec::new(),
            },
            inspector,
            inspection_sequence: 0,
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
                "limits": {"mensagem": database.limits.message,
                    "estado": database.limits.state, "resposta": database.limits.response}
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

    fn request(&mut self, body: &[u8]) -> Vec<u8> {
        let proposal = self.propose(body);
        let diagnostic = proposal
            .as_ref()
            .err()
            .map(|error| serde_json::json!({"code": error.code, "message": error.message}));
        let response = self.published.finish(proposal);
        self.inspection_sequence += 1;
        self.inspect(serde_json::json!({"event": "completed", "diagnostic": diagnostic}));
        response
    }

    fn preprocess(&self, program: &Program, input: &[u8]) -> Result<Vec<u8>> {
        let output = program.run(input)?;
        if !matches!(output.first(), Some(0 | 1)) {
            return Err(Error::new("HOST_TRANSPORT", "invalid preprocessing result"));
        }
        Ok(output)
    }

    fn propose(&mut self, body: &[u8]) -> Result<(Vec<u8>, Option<Vec<u8>>)> {
        let input = packet(&self.published.state, body);
        let decoded = self.preprocess(&self.decode, &input)?;
        if decoded[0] == 0 {
            return Ok((decoded[1..].to_vec(), None));
        }
        let authenticated = self.preprocess(&self.authenticate, &input)?;
        if authenticated[0] == 0 {
            return Ok((authenticated[1..].to_vec(), None));
        }
        let (code, rest) = split(&authenticated[1..])?;
        let (proof, rest) = split(rest)?;
        let (instance, bindings) = split(rest)?;
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
                "execute".into(),
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
        let output = program.run(&input)?;
        let proposal = checked_proposal(&output, &self.limits)?;
        request.remove()?;
        Ok(proposal)
    }

    fn serve(&mut self) -> Result<()> {
        serve_stream(
            &mut io::stdin().lock(),
            &mut io::stdout().lock(),
            self.limits.message,
            |body| self.request(body),
        )
    }
}

fn serve_stream(
    input: &mut impl Read,
    output: &mut impl Write,
    limit: u64,
    mut request: impl FnMut(&[u8]) -> Vec<u8>,
) -> Result<()> {
    loop {
        let mut header = [0; 8];
        let quantity = read_up_to(input, &mut header)?;
        if quantity == 0 {
            return Ok(());
        }
        let terminal = if quantity != 8 {
            Some("entrada")
        } else if u64::from_be_bytes(header) > limit {
            Some("limite")
        } else {
            None
        };
        if let Some(status) = terminal {
            output.write_all(&error_frame(status))?;
            output.flush()?;
            return Ok(());
        }
        let size = usize::try_from(u64::from_be_bytes(header))
            .map_err(|_| Error::new("HOST_TRANSPORT", "message length is not representable"))?;
        let mut body = vec![0; size];
        if read_up_to(input, &mut body)? != size {
            output.write_all(&error_frame("entrada"))?;
            output.flush()?;
            return Ok(());
        }
        output.write_all(&request(&body))?;
        output.flush()?;
    }
}

fn read_up_to(reader: &mut impl Read, mut buffer: &mut [u8]) -> io::Result<usize> {
    let expected = buffer.len();
    while !buffer.is_empty() {
        match reader.read(buffer) {
            Ok(0) => break,
            Ok(quantity) => buffer = &mut buffer[quantity..],
            Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
            Err(error) => return Err(error),
        }
    }
    Ok(expected - buffer.len())
}

struct Options {
    root: PathBuf,
    configuration: PathBuf,
    seed: PathBuf,
    source: PathBuf,
    kernel: PathBuf,
    inspect_socket: Option<PathBuf>,
}

impl Options {
    fn read() -> Result<Option<Self>> {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let lock: Value =
            serde_json::from_str(include_str!("../tools/admission/toolchain.lock.json"))?;
        let mut configuration = None;
        let mut seed = None;
        let mut inspect_socket = None;
        let mut source = root.join(format!(".tools/bend-source-{}", text(&lock, "version")?));
        let mut kernel = root.join(format!(".tools/bendtt-{}", text(&lock, "kernelSha256")?));
        let mut arguments = std::env::args_os().skip(1);
        while let Some(argument) = arguments.next() {
            if argument == "--help" || argument == "-h" {
                println!(
                    "Usage: jaydb2 --configuration FILE --seed FILE [--bend-source DIR] [--bendtt FILE] [--inspect-socket ADMIN_SOCKET]"
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
                _ => {
                    return Err(Error::new(
                        "ARGUMENT",
                        format!("unknown option {}", argument.to_string_lossy()),
                    ));
                }
            }
        }
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
            error_frame("entrada"),
            hex(
                "0000000000000037060000000000000002040000000000000006737461747573040000000000000007656e747261646104000000000000000576616c6f7200"
            )
        );
        assert_eq!(
            error_frame("falha"),
            hex(
                "000000000000003506000000000000000204000000000000000673746174757304000000000000000566616c686104000000000000000576616c6f7200"
            )
        );
        assert_eq!(
            Error::new("PRIMARY_CHECK", "proof rejected").response(),
            error_frame("certificado")
        );
        assert_eq!(
            Error::new("NATIVE", "child exited").response(),
            error_frame("falha")
        );
        assert!(split(&[0; 7]).is_err());
        assert!(split(&8u64.to_be_bytes()).is_err());
    }

    #[test]
    fn framing_preserves_the_next_request_and_stops_on_unknown_extent() {
        let mut seen = Vec::new();
        let mut response = Vec::new();
        let incoming = packet(b"bad", &packet(b"next", &[]));
        serve_stream(&mut Cursor::new(incoming), &mut response, 4, |body| {
            seen.push(body.to_vec());
            error_frame(if body == b"bad" { "entrada" } else { "recusa" })
        })
        .unwrap();
        assert_eq!(seen, [b"bad".to_vec(), b"next".to_vec()]);
        assert_eq!(
            response,
            [error_frame("entrada"), error_frame("recusa")].concat()
        );
        for (incoming, status) in [
            (vec![0; 7], "entrada"),
            (5u64.to_be_bytes().to_vec(), "limite"),
            (packet(b"four", &[])[..9].to_vec(), "entrada"),
        ] {
            let mut response = Vec::new();
            serve_stream(&mut Cursor::new(incoming), &mut response, 4, |_| {
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
            response: error_frame("sucesso").len() as u64 - 8,
        };
        let mut published = Published {
            state: b"old".to_vec(),
            response: Vec::new(),
        };
        let success = [vec![1], packet(b"new", &error_frame("sucesso"))].concat();
        assert_eq!(
            published.finish(checked_proposal(&success, &limits)),
            error_frame("sucesso")
        );
        let refusal = [vec![0], error_frame("recusa")].concat();
        assert_eq!(
            published.finish(checked_proposal(&refusal, &limits)),
            error_frame("recusa")
        );
        for invalid in [
            vec![],
            vec![2],
            vec![1, 0],
            [vec![0], error_frame("certificado")].concat(),
            [vec![1], packet(b"long", &error_frame("sucesso"))].concat(),
            [vec![1], packet(b"new", &error_frame("certificado"))].concat(),
            [vec![1], packet(b"new", b"unframed")].concat(),
            [
                vec![1],
                packet(b"new", &[error_frame("sucesso"), vec![0]].concat()),
            ]
            .concat(),
        ] {
            assert_eq!(
                published.finish(checked_proposal(&invalid, &limits)),
                error_frame("falha")
            );
            assert_eq!(published.state, b"new");
            assert_eq!(published.response, error_frame("sucesso"));
        }
        assert_eq!(
            published.finish(Err(Error::new("PRIMARY_CHECK", "rejected"))),
            error_frame("certificado")
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
            &mut Cursor::new(packet(b"call", &[])),
            &mut BrokenOutput,
            4,
            |_| published.finish(Ok((error_frame("sucesso"), Some(b"new".to_vec())))),
        );
        assert!(result.is_err());
        assert_eq!(published.state, b"new");
        assert_eq!(published.response, error_frame("sucesso"));
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
