//! Private framed transport for checked, stateless Bend programs.
use crate::store::{self, Answer, Operation, Snapshot, Transaction, Value};
use crate::{Error, Limits, Program, Result, split};
use std::collections::VecDeque;
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

pub struct IdleWorkers {
    limit: usize,
    workers: VecDeque<(String, Worker)>,
}

impl IdleWorkers {
    pub fn new(limit: usize) -> Self {
        Self {
            limit,
            workers: VecDeque::new(),
        }
    }

    pub fn take(&mut self, handle: &str) -> Option<Worker> {
        let index = self.workers.iter().rposition(|(key, _)| key == handle)?;
        self.workers.remove(index).map(|(_, worker)| worker)
    }

    pub fn put(&mut self, handle: &str, worker: Worker) -> Option<Worker> {
        self.workers.push_back((handle.to_owned(), worker));
        if self.workers.len() > self.limit {
            self.workers.pop_front().map(|(_, worker)| worker)
        } else {
            None
        }
    }

    pub fn remove(&mut self, handle: &str) {
        self.workers.retain(|(key, _)| key != handle);
    }

    pub fn clear(&mut self) {
        self.workers.clear();
    }
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
        // Append keeps the child's next write at EOF when a completed CUDA
        // exchange clears the file, regardless of its old descriptor offset.
        if program.gpu.is_some() && unsafe { libc::fcntl(fd, libc::F_SETFL, libc::O_APPEND) } == -1
        {
            return Err(io::Error::last_os_error().into());
        }
        let mut command = program.command(threads);
        command
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(errors.try_clone()?);
        let child = command.spawn();
        #[cfg(test)]
        let child = {
            let mut attempt = child;
            // A parallel test can fork while a generated script is open for
            // writing. Linux rejects exec until that child closes its copy.
            for _ in 0..20 {
                if !attempt
                    .as_ref()
                    .is_err_and(|error| error.raw_os_error() == Some(libc::ETXTBSY))
                {
                    break;
                }
                std::thread::sleep(std::time::Duration::from_millis(10));
                attempt = command.spawn();
            }
            attempt
        };
        let mut child = child?;
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
            self.check_gpu_diagnostics()?;
            program.validate()?;
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
            // Physical host bound only. A program may legally write a value
            // larger than the state limit and remove it again before finishing;
            // the state limit is checked at commit, as R.finalize does.
            const OPERATION_MAX: u64 = 1 << 30;
            match tag[0] {
                2 if size - 1 > OPERATION_MAX => {
                    return Err(protocol("live operation exceeds the frame budget"));
                }
                0 | 1 | 3 if size - 1 > limits.response.saturating_add(8) => {
                    return Err(protocol("live response exceeds the configured limit"));
                }
                0..=3 => (),
                _ => return Err(protocol("unknown live frame tag")),
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

    fn check_gpu_diagnostics(&self) -> Result<()> {
        const NOTICE: &[u8] = b"bend: compiling the GPU program";
        const OVERLAP: usize = NOTICE.len() - 1;
        let size = self.errors.metadata()?.len();
        if size == 0 {
            return Ok(());
        }
        let mut buffer = [0; 8192];
        let mut offset = 0;
        while offset < size {
            let length = (size - offset).min(buffer.len() as u64) as usize;
            self.errors.read_exact_at(&mut buffer[..length], offset)?;
            if buffer[..length]
                .windows(NOTICE.len())
                .any(|window| window == NOTICE)
            {
                return Err(Error::new(
                    "GPU_REBUILD",
                    "GPU artifact is incompatible; prepare again",
                ));
            }
            if offset + length as u64 == size {
                break;
            }
            offset += (length - OVERLAP) as u64;
        }
        // Bend completes its CUDA diagnostics before sending the final frame.
        // Keep no stderr history from completed exchanges on a reused worker.
        self.errors.set_len(0)?;
        Ok(())
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Temporary, error_frame, packet};
    use sha2::{Digest, Sha256};
    use std::fs;
    use std::os::unix::fs::PermissionsExt;

    fn script(directory: &Temporary, name: &str, body: &str) -> Program {
        let path = directory.path.join(name);
        let bytes = format!("#!/bin/sh\n{body}\n");
        fs::write(&path, &bytes).unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).unwrap();
        Program {
            path,
            sha256: format!("{:x}", Sha256::digest(bytes)),
            gpu: None,
        }
    }

    #[test]
    fn idle_workers_are_evicted_in_lru_order_across_handles() {
        let directory = Temporary::new(&std::env::temp_dir(), "jaydb-idle-test").unwrap();
        let program = script(&directory, "idle", "read -r request");
        let mut idle = IdleWorkers::new(2);
        let first = Worker::spawn(&program, 1).unwrap();
        let second = Worker::spawn(&program, 1).unwrap();
        let second_pid = second.child.id();
        assert!(idle.put("first", first).is_none());
        assert!(idle.put("second", second).is_none());
        let reused = idle.take("first").unwrap();
        assert!(idle.put("first", reused).is_none());

        let third = Worker::spawn(&program, 1).unwrap();
        let evicted = idle.put("third", third).unwrap();
        assert_eq!(evicted.child.id(), second_pid);
        drop(evicted);
        assert!(idle.take("second").is_none());
        assert_eq!(idle.workers.len(), 2);
        assert!(idle.take("first").is_some());
        idle.remove("third");
        assert!(idle.workers.is_empty());
    }

    #[test]
    fn oversized_operation_retires_worker_before_reading_payload() {
        fn emit(bytes: &[u8]) -> String {
            let octets: String = bytes.iter().map(|byte| format!("\\{byte:03o}")).collect();
            format!("dd bs=1 count=8 of=/dev/null 2>/dev/null\nprintf '{octets}'")
        }

        let directory = Temporary::new(&std::env::temp_dir(), "jaydb-frame-test").unwrap();
        let limits = Limits {
            message: 128,
            state: 256,
            response: 128,
        };
        let snapshot =
            Snapshot::empty(store::Schema::new(vec![], limits.state).unwrap(), 0).unwrap();
        let initial = snapshot.save();
        let oversized_header = [((1u64 << 30) + 2).to_be_bytes().as_slice(), &[2]].concat();
        let bad = script(&directory, "oversize", &emit(&oversized_header));
        let mut worker = Worker::spawn(&bad, 1).unwrap();
        let Err(error) = worker.run(&bad, true, b"", &snapshot, &limits) else {
            panic!("oversized declaration reached the transaction");
        };
        assert_eq!(error.code, "HOST_TRANSPORT");
        assert_eq!(error.message, "live operation exceeds the frame budget");
        assert!(worker.child.try_wait().unwrap().is_some());
        assert_eq!(snapshot.save(), initial);

        let response = error_frame("input");
        let good_frame = packet(&[&[0], response.as_slice()].concat(), &[]);
        let good = script(&directory, "valid", &emit(&good_frame));
        let mut worker = Worker::spawn(&good, 1).unwrap();
        let Decision::Keep { response: actual } =
            worker.run(&good, true, b"", &snapshot, &limits).unwrap()
        else {
            panic!("expected worker to return the input response");
        };
        assert_eq!(actual, response);
    }
}
