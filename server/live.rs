//! Private framed transport for checked, stateless Bend programs.
use crate::store::{self, Answer, Operation, Snapshot, Transaction, Value};
use crate::{Error, Limits, Program, Result, split};
use std::fs::File;
use std::io::{self, BufReader, IoSlice, Read, Write};
use std::os::fd::{AsRawFd, FromRawFd};
use std::os::unix::fs::FileExt;
use std::process::{Child, ChildStdin, ChildStdout, Stdio};

pub enum Decision {
    Keep {
        response: Vec<u8>,
    },
    Success {
        transaction: Transaction,
        response: Vec<u8>,
        commit: bool,
    },
}

pub struct Worker {
    child: Child,
    input: ChildStdin,
    output: BufReader<ChildStdout>,
    errors: File,
}

impl Worker {
    pub fn spawn(program: &Program, threads: usize) -> Result<Self> {
        program.validate()?;
        // An unlinked file cannot fill a pipe while the host waits for a frame.
        // It also lets the host inspect CUDA's synchronous rebuild diagnostic
        // before accepting the final frame.
        let fd = unsafe { libc::memfd_create(c"jaydb-worker-stderr".as_ptr(), libc::MFD_CLOEXEC) };
        if fd == -1 {
            return Err(io::Error::last_os_error().into());
        }
        let errors = unsafe { File::from_raw_fd(fd) };
        let mut child = program
            .command(threads)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(errors.try_clone()?)
            .spawn()?;
        Ok(Self {
            input: child.stdin.take().expect("piped stdin"),
            output: BufReader::new(child.stdout.take().expect("piped stdout")),
            child,
            errors,
        })
    }

    pub fn run(
        &mut self,
        program: &Program,
        single: bool,
        request: &[u8],
        snapshot: &Snapshot,
        limits: &Limits,
    ) -> Result<Decision> {
        let decision = match self.exchange(single, request, snapshot, limits) {
            Ok(decision) => decision,
            Err(mut error) => {
                self.stop();
                let stderr = self.diagnostics();
                if !stderr.is_empty() {
                    error.message.push_str(": ");
                    error.message.push_str(&stderr);
                }
                return Err(error);
            }
        };
        if program.gpu.is_some() {
            program.validate()?;
            if self
                .diagnostics()
                .contains("bend: compiling the GPU program")
            {
                return Err(Error::new(
                    "GPU_REBUILD",
                    "GPU artifact is incompatible; prepare again",
                ));
            }
        }
        Ok(decision)
    }

    fn exchange(
        &mut self,
        single: bool,
        request: &[u8],
        snapshot: &Snapshot,
        limits: &Limits,
    ) -> Result<Decision> {
        self.check_idle()?;
        self.write_frame(request)?;
        let mut transaction = snapshot.begin();
        let mut asked_authentication = false;
        let mut may_operate = false;

        loop {
            let mut header = [0; 8];
            self.output.read_exact(&mut header).map_err(worker_io)?;
            let size = u64::from_be_bytes(header);
            if size == 0 || size > isize::MAX as u64 {
                return Err(protocol("invalid live frame length"));
            }
            let mut tag = [0];
            self.output.read_exact(&mut tag).map_err(worker_io)?;
            let frame_limit = match tag[0] {
                2 => size - 1,
                0 | 1 | 3 => limits.response.saturating_add(8),
                _ => return Err(protocol("unknown live frame tag")),
            };
            if size - 1 > frame_limit {
                return Err(protocol("live response exceeds the configured limit"));
            }
            let mut payload = Vec::new();
            self.output
                .by_ref()
                .take(size - 1)
                .read_to_end(&mut payload)
                .map_err(worker_io)?;
            if payload.len() as u64 != size - 1 {
                return Err(protocol("truncated live frame"));
            }

            if tag[0] == 2 {
                let operation =
                    Operation::decode(&payload).map_err(|err| protocol(err.to_string()))?;
                if matches!(operation, Operation::Authenticate { .. }) {
                    if asked_authentication {
                        return Err(protocol("repeated live authentication"));
                    }
                    asked_authentication = true;
                } else if !may_operate {
                    return Err(protocol("unexpected live operation"));
                }
                let answer = transaction.operate(operation);
                match answer {
                    Answer::User(_) => may_operate = true,
                    Answer::NoUser | Answer::FailureData => may_operate = false,
                    _ => {}
                }
                self.write_frame(&answer.encode())?;
                continue;
            }

            let status = response_status(&payload)?;
            match (tag[0], status.as_str()) {
                (1, "success") | (3, "limit" | "data") if may_operate => (),
                (
                    0,
                    "input" | "authentication" | "certificate" | "data" | "limit" | "failure"
                    | "refusal",
                ) => (),
                _ => return Err(protocol("invalid live final tag or status")),
            }
            if single {
                if self.output.read(&mut [0]).map_err(worker_io)? != 0 {
                    return Err(protocol(
                        "unexpected output after direct worker final frame",
                    ));
                }
                let status = self.child.wait().map_err(worker_io)?;
                if !status.success() {
                    return Err(Error::new("NATIVE", format!("worker {status}")));
                }
            } else {
                self.check_idle()?;
            }
            return Ok(if tag[0] == 0 {
                Decision::Keep { response: payload }
            } else {
                Decision::Success {
                    transaction,
                    response: payload,
                    commit: tag[0] == 1,
                }
            });
        }
    }

    fn check_idle(&mut self) -> Result<()> {
        if let Some(status) = self.child.try_wait().map_err(worker_io)? {
            return Err(Error::new("NATIVE", format!("worker {status}")));
        }
        if !self.output.buffer().is_empty() {
            return Err(protocol("unsolicited output or closed live worker"));
        }
        let mut descriptor = libc::pollfd {
            fd: self.output.get_ref().as_raw_fd(),
            events: libc::POLLIN,
            revents: 0,
        };
        loop {
            match unsafe { libc::poll(&mut descriptor, 1, 0) } {
                0 => return Ok(()),
                1 => return Err(protocol("unsolicited output or closed live worker")),
                _ => {
                    let error = io::Error::last_os_error();
                    if error.kind() != io::ErrorKind::Interrupted {
                        return Err(worker_io(error));
                    }
                }
            }
        }
    }

    fn write_frame(&mut self, body: &[u8]) -> Result<()> {
        let header = (body.len() as u64).to_be_bytes();
        let mut parts = &mut [IoSlice::new(&header), IoSlice::new(body)][..];
        while !parts.is_empty() {
            match self.input.write_vectored(parts) {
                Ok(0) => return Err(worker_io(io::ErrorKind::WriteZero.into())),
                Ok(n) => IoSlice::advance_slices(&mut parts, n),
                Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                Err(error) => return Err(worker_io(error)),
            }
        }
        Ok(())
    }

    fn diagnostics(&self) -> String {
        const MAX: u64 = 64 * 1024;
        let size = self.errors.metadata().map_or(0, |metadata| metadata.len());
        let mut bytes = vec![0; size.min(MAX) as usize];
        let _ = self
            .errors
            .read_exact_at(&mut bytes, size.saturating_sub(MAX));
        String::from_utf8_lossy(&bytes).into_owned()
    }

    fn stop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

impl Drop for Worker {
    fn drop(&mut self) {
        self.stop();
    }
}

fn response_status(response: &[u8]) -> Result<String> {
    let (body, rest) = split(response)?;
    if !rest.is_empty() {
        return Err(protocol("trailing data after live response"));
    }
    let value = store::decode(body).map_err(|err| protocol(err.to_string()))?;
    let Value::Record(fields) = &value else {
        return Err(protocol("invalid live response record"));
    };
    match fields.as_slice() {
        [(status, Value::Text(name)), (value, payload)]
            if status == "status"
                && value == "value"
                && (matches!(name.as_str(), "success" | "refusal")
                    || matches!(payload, Value::Absent)) =>
        {
            Ok(name.clone())
        }
        _ => Err(protocol("invalid live response shape")),
    }
}

fn worker_io(error: io::Error) -> Error {
    Error::new("NATIVE", format!("live worker: {error}"))
}

fn protocol(message: impl Into<String>) -> Error {
    Error::new("HOST_TRANSPORT", message)
}
