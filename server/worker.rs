//! Authoritative admitted ELF images and single-use, data-free idle children.
use crate::{Error, Result, capture, diagnostic};
use sha2::{Digest, Sha256};
use std::fs::File;
use std::io::{Read, Seek, SeekFrom};
use std::os::fd::{AsRawFd, FromRawFd};
use std::path::Path;
use std::process::Command;
use std::sync::{Arc, Condvar, Mutex};
use std::thread::JoinHandle;

pub(crate) struct Image(File);

impl Image {
    pub(crate) fn load(path: &Path, expected: &str) -> Result<Self> {
        // SAFETY: constant NUL-terminated name and documented Linux flags.
        let fd = unsafe {
            libc::memfd_create(
                c"jaydb-admitted".as_ptr(),
                libc::MFD_CLOEXEC | libc::MFD_ALLOW_SEALING,
            )
        };
        if fd < 0 {
            return Err(std::io::Error::last_os_error().into());
        }
        // SAFETY: successful memfd_create returns a new owned descriptor.
        let mut file = unsafe { File::from_raw_fd(fd) };
        std::io::copy(&mut File::open(path)?, &mut file)?;
        let seals =
            libc::F_SEAL_WRITE | libc::F_SEAL_GROW | libc::F_SEAL_SHRINK | libc::F_SEAL_SEAL;
        // SAFETY: owned live fd; integer fcntl arguments, no pointers.
        if unsafe { libc::fcntl(fd, libc::F_ADD_SEALS, seals) } != 0
            || unsafe { libc::fcntl(fd, libc::F_GET_SEALS) } != seals
        {
            return Err(Error::new("HOST_NATIVE", "cannot seal admitted executable"));
        }
        // Hash the now immutable image itself, never the earlier path read.
        file.seek(SeekFrom::Start(0))?;
        let mut magic = [0; 4];
        file.read_exact(&mut magic)?;
        if magic != *b"\x7fELF" {
            return Err(Error::new("HOST_NATIVE", "admitted executable is not ELF"));
        }
        file.seek(SeekFrom::Start(0))?;
        let mut hash = Sha256::new();
        std::io::copy(&mut file, &mut hash)?;
        if format!("{:x}", hash.finalize()) != expected {
            return Err(Error::new(
                "HOST_NATIVE",
                "official executable hash mismatch",
            ));
        }
        Ok(Self(file))
    }

    pub(crate) fn command(&self, threads: usize) -> Command {
        // Keep this Image alive through spawn. CLOEXEC closes the fd only after
        // the kernel opens this exact ELF. No pre_exec: retain posix_spawn.
        command(
            Path::new(&format!("/proc/self/fd/{}", self.0.as_raw_fd())),
            threads,
        )
    }
}

fn command(path: &Path, threads: usize) -> Command {
    let mut command = Command::new(path);
    command
        .env("BENDRTS", "")
        .args(["+RTS", "--threads"])
        .arg(threads.to_string())
        .args(["--gpu", "off", "-RTS"]);
    command
}

#[derive(Default)]
struct Slot {
    idle: Option<capture::ChildGuard>,
    refill: bool,
    stop: bool,
}

pub(crate) struct Pool {
    image: Arc<Image>,
    shared: Arc<(Mutex<Slot>, Condvar)>,
    refill: Option<JoinHandle<()>>,
    threads: usize,
}

impl Pool {
    pub(crate) fn new(image: Arc<Image>, threads: usize) -> Result<Self> {
        let shared = Arc::new((
            Mutex::new(Slot {
                refill: true,
                ..Slot::default()
            }),
            Condvar::new(),
        ));
        let state = Arc::clone(&shared);
        let worker_image = Arc::clone(&image);
        let refill = std::thread::Builder::new()
            .name("jaydb2-refill".into())
            .spawn(move || {
                let (mutex, wake) = &*state;
                loop {
                    let mut slot = mutex.lock().unwrap();
                    while !slot.refill && !slot.stop {
                        slot = wake.wait(slot).unwrap();
                    }
                    if slot.stop {
                        break;
                    }
                    slot.refill = false;
                    drop(slot);
                    // No packet, root, registry or credential is held by this thread.
                    let child = capture::spawn(&mut worker_image.command(threads));
                    let mut slot = mutex.lock().unwrap();
                    if slot.stop {
                        drop(child);
                        break;
                    }
                    match child {
                        Ok(child) => slot.idle = Some(child),
                        Err(error) => diagnostic(format_args!(
                            "idle worker spawn: {error:?}; next call uses fresh spawn"
                        )),
                    }
                    // A selection during spawn already has a fresh child. This
                    // completed spawn fills its one idle slot; do not spawn again.
                    slot.refill = false;
                    wake.notify_all();
                }
            })?;
        Ok(Self {
            image,
            shared,
            refill: Some(refill),
            threads,
        })
    }

    pub(crate) fn take(&self, threads: usize) -> Result<capture::ChildGuard> {
        assert_eq!(threads, self.threads, "pool runtime policy changed");
        let (mutex, wake) = &*self.shared;
        let mut slot = mutex.lock().unwrap();
        let idle = slot.idle.take();
        slot.refill = true;
        wake.notify_one();
        drop(slot);
        if let Some(mut child) = idle {
            match child.0.as_mut().expect("owned idle child").try_wait() {
                Ok(None) => return Ok(child),
                Ok(Some(_)) => {} // Reaped; discard and launch this call fresh.
                Err(error) => diagnostic(format_args!("idle worker status: {error}")),
            }
            drop(child); // Kill/reap on status error as well.
        }
        capture::spawn(&mut self.image.command(threads))
    }
}

impl Drop for Pool {
    fn drop(&mut self) {
        let (mutex, wake) = &*self.shared;
        let mut slot = mutex.lock().unwrap();
        slot.stop = true;
        wake.notify_one();
        drop(slot);
        if self.refill.take().expect("refill thread").join().is_err() {
            diagnostic(format_args!("idle worker refill panicked"));
            std::process::abort();
        }
        // Drop outside the mutex, after in-flight spawn has ended. ChildGuard
        // kills and reaps before invalidation/shutdown returns.
        let idle = mutex.lock().unwrap().idle.take();
        drop(idle);
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::Temporary;
    use std::os::unix::fs::FileExt;
    use std::path::PathBuf;
    use std::sync::OnceLock;
    use std::time::Duration;

    pub(crate) fn fixture() -> PathBuf {
        static FIXTURE: OnceLock<(Temporary, PathBuf)> = OnceLock::new();
        FIXTURE
            .get_or_init(|| {
                let directory =
                    Temporary::new(&std::env::temp_dir(), "jaydb-pool-fixture").unwrap();
                let source = Path::new(env!("CARGO_MANIFEST_DIR"))
                    .join("tests/service/runtime_policy_worker.c");
                let path = directory.path.join("worker");
                assert!(
                    Command::new("clang-19")
                        .arg(source)
                        .arg("-o")
                        .arg(&path)
                        .status()
                        .unwrap()
                        .success()
                );
                (directory, path)
            })
            .1
            .clone()
    }

    pub(crate) fn hash(path: &Path) -> String {
        format!("{:x}", Sha256::digest(std::fs::read(path).unwrap()))
    }

    fn image() -> Arc<Image> {
        let path = fixture();
        Arc::new(Image::load(&path, &hash(&path)).unwrap())
    }

    fn ready(pool: &Pool) -> u32 {
        let (mutex, wake) = &*pool.shared;
        let (mut slot, timeout) = wake
            .wait_timeout_while(mutex.lock().unwrap(), Duration::from_secs(5), |slot| {
                slot.idle.is_none()
            })
            .unwrap();
        assert!(!timeout.timed_out(), "idle worker was not spawned");
        let child = slot.idle.as_mut().unwrap().0.as_mut().unwrap();
        assert!(child.try_wait().unwrap().is_none());
        child.id()
    }

    fn reaped(pid: u32) {
        // SAFETY: waitpid uses no user pointer and WNOHANG cannot block.
        assert_eq!(
            unsafe { libc::waitpid(pid as i32, std::ptr::null_mut(), libc::WNOHANG) },
            -1
        );
        assert_eq!(
            std::io::Error::last_os_error().raw_os_error(),
            Some(libc::ECHILD)
        );
    }

    #[test]
    fn image_seals_reject_writes_growth_truncation_and_further_seals() {
        let image = image();
        assert_eq!(
            image.0.write_at(b"x", 0).unwrap_err().raw_os_error(),
            Some(libc::EPERM)
        );
        let len = image.0.metadata().unwrap().len();
        for size in [0, len + 1] {
            assert_eq!(
                image.0.set_len(size).unwrap_err().raw_os_error(),
                Some(libc::EPERM)
            );
        }
        // SAFETY: owned descriptor and integer fcntl arguments.
        assert_eq!(
            unsafe { libc::fcntl(image.0.as_raw_fd(), libc::F_ADD_SEALS, libc::F_SEAL_WRITE) },
            -1
        );
        assert_eq!(
            std::io::Error::last_os_error().raw_os_error(),
            Some(libc::EPERM)
        );
        assert_ne!(
            unsafe { libc::fcntl(image.0.as_raw_fd(), libc::F_GETFD) } & libc::FD_CLOEXEC,
            0
        );
    }

    #[test]
    fn dead_idle_child_falls_back_to_fresh_request_and_is_reaped() {
        let image = image();
        let pool = Pool::new(Arc::clone(&image), 1).unwrap();
        let pid = ready(&pool);
        {
            let mut slot = pool.shared.0.lock().unwrap();
            let child = slot.idle.as_mut().unwrap().0.as_mut().unwrap();
            child.kill().unwrap();
            child.wait().unwrap();
        }
        let child = pool.take(1).unwrap();
        assert_ne!(child.0.as_ref().unwrap().id(), pid);
        let output = capture::capture_child(child, b"current root and request").unwrap();
        assert!(output.status.success());
        assert_eq!(output.stdout, b"current root and request");
        reaped(pid);
    }

    #[test]
    fn invalidation_and_shutdown_reap_idle_children_and_close_pipes() {
        let image = image();
        let pool = Pool::new(image, 1).unwrap();
        let pid = ready(&pool);
        let stdin = pool
            .shared
            .0
            .lock()
            .unwrap()
            .idle
            .as_mut()
            .unwrap()
            .0
            .as_mut()
            .unwrap()
            .stdin
            .take()
            .unwrap();
        drop(pool); // Same drop path used by registration invalidation and shutdown.
        reaped(pid);
        use std::io::Write;
        assert_eq!(
            (&stdin).write_all(b"must not execute").unwrap_err().kind(),
            std::io::ErrorKind::BrokenPipe
        );
    }

    #[test]
    fn many_sequential_calls_use_each_child_once_and_leave_no_request_in_idle_slot() {
        let image = image();
        let pool = Pool::new(Arc::clone(&image), 1).unwrap();
        let mut pids = std::collections::HashSet::new();
        for i in 0..100 {
            ready(&pool);
            let child = pool.take(1).unwrap();
            let pid = child.0.as_ref().unwrap().id();
            assert!(pids.insert(pid));
            let packet = vec![i; 128 * 1024];
            let output = capture::capture_child(child, &packet).unwrap();
            assert!(output.status.success());
            assert_eq!(output.stdout, packet);
            reaped(pid);
        }
        let pid = ready(&pool);
        drop(pool);
        reaped(pid);
    }

    #[test]
    fn idle_spawn_failure_leaves_fresh_spawn_error_and_shutdown_safe() {
        let directory = Temporary::new(&std::env::temp_dir(), "jaydb-bad-elf").unwrap();
        let path = directory.path.join("invalid-elf");
        std::fs::write(&path, b"\x7fELF not an executable").unwrap();
        let image = Arc::new(Image::load(&path, &hash(&path)).unwrap());
        let pool = Pool::new(Arc::clone(&image), 1).unwrap();
        // Both speculative and selected launches fail. Never turn an empty
        // slot into success, reuse another artifact, or retry delivered input.
        assert_eq!(pool.take(1).err().unwrap().code, "HOST_IO");
        drop(pool);
    }

    #[test]
    fn missing_idle_slot_falls_back_without_waiting_for_refill() {
        let image = image();
        let pool = Pool::new(Arc::clone(&image), 1).unwrap();
        ready(&pool);
        drop(pool.shared.0.lock().unwrap().idle.take());
        let child = pool.take(1).unwrap();
        assert_eq!(
            capture::capture_child(child, b"fresh").unwrap().stdout,
            b"fresh"
        );
    }
}
