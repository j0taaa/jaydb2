//! Binary helper transport. Reap the direct child before scope exit joins pipes.
use crate::{Error, Result};
use std::io::{self, Read, Write};
use std::process::{Child, Command, ExitStatus, Output, Stdio};

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
                eprintln!("jaydb2: cannot reap helper: {error}");
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
    mut before_spawn: impl FnMut(Pipe, u32) -> io::Result<()>,
) -> Result<Output> {
    std::thread::scope(|scope| {
        // This guard MUST live inside the scope closure: on error or unwind it
        // kills/reaps before the scope implicitly joins already-started pipes.
        let mut child = ChildGuard(Some(
            command
                .env("BEND_NO_TELEMETRY", "1")
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()?,
        ));
        let owned = child.0.as_mut().expect("spawned child");
        let pid = owned.id();
        let mut stdin = owned.stdin.take().expect("piped child stdin");
        let mut stdout = owned.stdout.take().expect("piped child stdout");
        let mut stderr = owned.stderr.take().expect("piped child stderr");
        let writer = before_spawn(Pipe::Input, pid)
            .and_then(|()| {
                std::thread::Builder::new()
                    .name("jaydb2-stdin".into())
                    .spawn_scoped(scope, move || stdin.write_all(input))
            })
            .map_err(setup_error)?;
        let reader = before_spawn(Pipe::Output, pid)
            .and_then(|()| {
                std::thread::Builder::new()
                    .name("jaydb2-stdout".into())
                    .spawn_scoped(scope, move || {
                        let mut bytes = Vec::new();
                        stdout.read_to_end(&mut bytes).map(|_| bytes)
                    })
            })
            .map_err(setup_error)?;
        let errors = before_spawn(Pipe::Error, pid)
            .and_then(|()| {
                std::thread::Builder::new()
                    .name("jaydb2-stderr".into())
                    .spawn_scoped(scope, move || {
                        let mut bytes = Vec::new();
                        stderr.read_to_end(&mut bytes).map(|_| bytes)
                    })
            })
            .map_err(setup_error)?;
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
    hook: impl FnMut(Pipe, u32) -> io::Result<()>,
) -> Result<Output> {
    let result = run(command, input, hook);
    if let Err(error) = &result
        && error.code == "HOST_PIPE_SETUP"
    {
        // Preserve the old fatal thread-startup policy, but only AFTER child
        // cleanup and pipe joins. Serial service stops; a read worker panic is
        // propagated as a fatal batch error, never a recoverable response.
        panic!("jaydb2: cannot start helper pipe thread: {}", error.message);
    }
    result
}

pub(crate) fn capture(command: &mut Command, input: &[u8]) -> Result<Output> {
    checked(command, input, |_, _| Ok(()))
}

#[cfg(test)]
pub(crate) fn inject_failure(command: &mut Command, input: &[u8], point: Pipe) -> Result<Output> {
    checked(command, input, |pipe, _| {
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
    use std::panic::{AssertUnwindSafe, catch_unwind};
    use std::time::{Duration, Instant};

    fn gone(pid: Option<u32>, start: Instant) {
        assert!(
            start.elapsed() < Duration::from_secs(10),
            "cleanup waited for the sleeping child to exit"
        );
        assert!(
            !std::path::Path::new(&format!("/proc/{}", pid.unwrap())).exists(),
            "helper still alive or unreaped"
        );
    }

    #[test]
    fn every_pipe_startup_error_reaps_before_joining_blocked_pipes() {
        let bytes = vec![0; 1024 * 1024];
        for point in [Pipe::Input, Pipe::Output, Pipe::Error] {
            let mut pid = None;
            let start = Instant::now();
            let result = run(Command::new("/bin/sleep").arg("30"), &bytes, |pipe, id| {
                pid = Some(id);
                if pipe == point {
                    Err(io::Error::other("injected resource exhaustion"))
                } else {
                    Ok(())
                }
            });
            assert_eq!(result.unwrap_err().code, "HOST_PIPE_SETUP");
            gone(pid, start);
        }
    }

    #[test]
    fn unwinding_at_every_pipe_start_reaps_before_scope_joins() {
        let bytes = vec![0; 1024 * 1024];
        for point in [Pipe::Input, Pipe::Output, Pipe::Error] {
            let mut pid = None;
            let start = Instant::now();
            let result = catch_unwind(AssertUnwindSafe(|| {
                run(Command::new("/bin/sleep").arg("30"), &bytes, |pipe, id| {
                    pid = Some(id);
                    assert_ne!(pipe, point, "injected unwind");
                    Ok(())
                })
            }));
            assert!(result.is_err());
            gone(pid, start);
        }
    }

    #[test]
    fn startup_failure_remains_fatal_after_cleanup() {
        for point in [Pipe::Input, Pipe::Output, Pipe::Error] {
            assert!(
                catch_unwind(|| {
                    inject_failure(Command::new("/bin/sleep").arg("30"), &[0; 8192], point)
                })
                .is_err()
            );
        }
    }
}
