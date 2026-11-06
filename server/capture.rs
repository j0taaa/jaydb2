//! Binary helper transport. Start pipe threads before launching any helper.
use crate::{Error, Result};
use std::io::{self, Read, Write};
use std::process::{
    Child, ChildStderr, ChildStdin, ChildStdout, Command, ExitStatus, Output, Stdio,
};
use std::sync::mpsc::sync_channel;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Pipe {
    Input,
    Output,
    Error,
}

struct ChildGuard(Option<Child>);

impl ChildGuard {
    fn wait(&mut self) -> io::Result<ExitStatus> {
        let status = self.0.as_mut().expect("owned child").wait()?;
        self.0 = None;
        Ok(status)
    }
}

impl Drop for ChildGuard {
    fn drop(&mut self) {
        if let Some(child) = &mut self.0 {
            let _ = child.kill(); // It may already have exited; still reap it.
            if let Err(error) = child.wait() {
                crate::diagnostic(format_args!("cannot reap helper: {error}"));
                std::process::abort();
            }
        }
    }
}

fn setup_error(error: io::Error) -> Error {
    Error::new("HOST_PIPE_SETUP", error.to_string())
}

fn run(
    command: &mut Command,
    input: &[u8],
    mut before_spawn: impl FnMut(Pipe) -> io::Result<()>,
) -> Result<Output> {
    std::thread::scope(|scope| {
        // All senders live INSIDE this closure. Any startup error or unwind
        // disconnects waiting threads before scope exit joins them. In
        // particular, no helper (or compiler descendant) exists when pipe
        // thread creation fails. Channels carry exactly one owned pipe each.
        let (send_input, receive_input) = sync_channel::<ChildStdin>(1);
        let (send_output, receive_output) = sync_channel::<ChildStdout>(1);
        let (send_error, receive_error) = sync_channel::<ChildStderr>(1);
        let writer = before_spawn(Pipe::Input)
            .and_then(|()| {
                std::thread::Builder::new()
                    .name("jaydb2-stdin".into())
                    .spawn_scoped(scope, move || match receive_input.recv() {
                        Ok(mut stdin) => stdin.write_all(input),
                        Err(_) => Ok(()), // Startup ended without a pipe handoff.
                    })
            })
            .map_err(setup_error)?;
        let reader = before_spawn(Pipe::Output)
            .and_then(|()| {
                std::thread::Builder::new()
                    .name("jaydb2-stdout".into())
                    .spawn_scoped(scope, move || {
                        let mut bytes = Vec::new();
                        if let Ok(mut stdout) = receive_output.recv() {
                            stdout.read_to_end(&mut bytes)?;
                        }
                        Ok::<_, io::Error>(bytes)
                    })
            })
            .map_err(setup_error)?;
        let errors = before_spawn(Pipe::Error)
            .and_then(|()| {
                std::thread::Builder::new()
                    .name("jaydb2-stderr".into())
                    .spawn_scoped(scope, move || {
                        let mut bytes = Vec::new();
                        if let Ok(mut stderr) = receive_error.recv() {
                            stderr.read_to_end(&mut bytes)?;
                        }
                        Ok::<_, io::Error>(bytes)
                    })
            })
            .map_err(setup_error)?;
        // Only launch after all fallible thread starts have succeeded. Retain
        // direct-child ownership inside the scope for subsequent errors.
        let mut child = ChildGuard(Some(
            command
                .env("BEND_NO_TELEMETRY", "1")
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()?,
        ));
        let owned = child.0.as_mut().expect("spawned child");
        send_input
            .send(owned.stdin.take().expect("piped child stdin"))
            .map_err(|_| Error::new("HOST_PIPE", "input worker stopped before handoff"))?;
        send_output
            .send(owned.stdout.take().expect("piped child stdout"))
            .map_err(|_| Error::new("HOST_PIPE", "output worker stopped before handoff"))?;
        send_error
            .send(owned.stderr.take().expect("piped child stderr"))
            .map_err(|_| Error::new("HOST_PIPE", "error worker stopped before handoff"))?;
        drop((send_input, send_output, send_error));
        let status = child.wait()?;
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

fn checked(
    command: &mut Command,
    input: &[u8],
    hook: impl FnMut(Pipe) -> io::Result<()>,
) -> Result<Output> {
    let result = run(command, input, hook);
    if let Err(error) = &result
        && error.code == "HOST_PIPE_SETUP"
    {
        // Preserve the fatal thread-startup policy after waiting-thread joins,
        // with no helper launched. Serial service stops; a read worker panic is
        // propagated as a fatal batch error, never a recoverable response.
        panic!("jaydb2: cannot start helper pipe thread: {}", error.message);
    }
    result
}

pub(crate) fn capture(command: &mut Command, input: &[u8]) -> Result<Output> {
    checked(command, input, |_| Ok(()))
}

#[cfg(test)]
pub(crate) fn inject_failure(command: &mut Command, input: &[u8], point: Pipe) -> Result<Output> {
    checked(command, input, |pipe| {
        if pipe == point {
            Err(io::Error::other("injected pipe startup failure"))
        } else {
            Ok(())
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::fd::AsRawFd;
    use std::os::unix::net::UnixStream;
    use std::os::unix::process::CommandExt;
    use std::panic::{AssertUnwindSafe, catch_unwind};
    use std::time::{Duration, Instant};

    fn launch_sentinel(program: &str) -> (Command, UnixStream, UnixStream) {
        let (observed, event) = UnixStream::pair().unwrap();
        observed.set_nonblocking(true).unwrap();
        let fd = event.as_raw_fd();
        let mut command = Command::new(program);
        // SAFETY: the callback performs only one async-signal-safe write with
        // a live inherited fd and a valid byte. The parent keeps `event` alive.
        // It runs before exec, so a successful spawn MUST leave the sentinel
        // byte before Command::spawn returns, without scheduler/timer guesses.
        unsafe {
            command.pre_exec(move || {
                let byte = [1u8];
                if libc::write(fd, byte.as_ptr().cast(), 1) != 1 {
                    return Err(io::Error::last_os_error());
                }
                Ok(())
            });
        }
        (command, observed, event)
    }

    fn no_helper_launch(observed: &mut UnixStream, start: Instant) {
        assert!(
            start.elapsed() < Duration::from_secs(3),
            "waiting pipe threads failed to shut down"
        );
        let mut byte = [0];
        assert!(
            matches!(observed.read(&mut byte), Err(e) if e.kind() == io::ErrorKind::WouldBlock),
            "helper launch occurred despite pipe-thread startup failure"
        );
    }

    fn expected_starts(point: Pipe) -> Vec<Pipe> {
        match point {
            Pipe::Input => vec![Pipe::Input],
            Pipe::Output => vec![Pipe::Input, Pipe::Output],
            Pipe::Error => vec![Pipe::Input, Pipe::Output, Pipe::Error],
        }
    }

    #[test]
    fn launch_sentinel_observes_a_real_helper() {
        let (mut command, mut observed, _event) = launch_sentinel("/bin/true");
        assert!(capture(&mut command, &[]).unwrap().status.success());
        let mut byte = [0];
        assert_eq!(observed.read(&mut byte).unwrap(), 1);
        assert_eq!(byte, [1]);
    }

    #[test]
    fn every_pipe_startup_error_joins_waiters_without_launching_a_helper() {
        let bytes = vec![0; 1024 * 1024];
        for point in [Pipe::Input, Pipe::Output, Pipe::Error] {
            let (mut command, mut observed, _event) = launch_sentinel("/bin/sleep");
            command.arg("30");
            let mut seen = Vec::new();
            let start = Instant::now();
            let result = run(&mut command, &bytes, |pipe| {
                seen.push(pipe);
                if pipe == point {
                    Err(io::Error::other("injected resource exhaustion"))
                } else {
                    Ok(())
                }
            });
            assert_eq!(result.unwrap_err().code, "HOST_PIPE_SETUP");
            assert_eq!(seen, expected_starts(point), "fault hook was not reached");
            no_helper_launch(&mut observed, start);
        }
    }

    #[test]
    fn unwinding_at_every_pipe_start_joins_waiters_without_launching_a_helper() {
        let bytes = vec![0; 1024 * 1024];
        for point in [Pipe::Input, Pipe::Output, Pipe::Error] {
            let (mut command, mut observed, _event) = launch_sentinel("/bin/sleep");
            command.arg("30");
            let mut seen = Vec::new();
            let start = Instant::now();
            let result = catch_unwind(AssertUnwindSafe(|| {
                run(&mut command, &bytes, |pipe| {
                    seen.push(pipe);
                    assert_ne!(pipe, point, "injected unwind");
                    Ok(())
                })
            }));
            assert!(result.is_err());
            assert_eq!(seen, expected_starts(point), "unwind hook was not reached");
            no_helper_launch(&mut observed, start);
        }
    }

    #[test]
    fn startup_failure_remains_fatal_without_launching_a_helper() {
        for point in [Pipe::Input, Pipe::Output, Pipe::Error] {
            let (mut command, mut observed, _event) = launch_sentinel("/bin/sleep");
            command.arg("30");
            let start = Instant::now();
            assert!(
                catch_unwind(AssertUnwindSafe(|| {
                    inject_failure(&mut command, &[0; 8192], point)
                }))
                .is_err()
            );
            no_helper_launch(&mut observed, start);
        }
    }

    #[test]
    fn failed_process_spawn_disconnects_and_joins_all_waiting_threads() {
        let directory = crate::Temporary::new(&std::env::temp_dir(), "jaydb-capture").unwrap();
        let mut seen = Vec::new();
        let start = Instant::now();
        let result = run(
            &mut Command::new(directory.path.join("missing-executable")),
            &[0; 8192],
            |point| {
                seen.push(point);
                Ok(())
            },
        );
        assert_eq!(result.unwrap_err().code, "HOST_IO");
        assert_eq!(seen, [Pipe::Input, Pipe::Output, Pipe::Error]);
        assert!(start.elapsed() < Duration::from_secs(3));
    }

    #[test]
    fn binary_input_and_large_stderr_drain_concurrently() {
        let input: Vec<_> = (0..1024 * 1024).map(|n| n as u8).collect();
        let output = capture(
            Command::new("python3").args([
                "-c",
                "import sys; data=sys.stdin.buffer.read(); sys.stdout.buffer.write(data); sys.stderr.buffer.write(bytes(262144))",
            ]),
            &input,
        )
        .unwrap();
        assert!(output.status.success());
        assert_eq!(output.stdout, input);
        assert_eq!(output.stderr, vec![0; 262144]);
    }

    #[test]
    fn unsuccessful_child_retains_status_despite_broken_input_pipe() {
        let output = capture(
            Command::new("/bin/sh").args(["-c", "exit 7"]),
            &[0; 1024 * 1024],
        )
        .unwrap();
        assert_eq!(output.status.code(), Some(7));
    }
}
