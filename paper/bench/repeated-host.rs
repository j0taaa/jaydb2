//! Research harness; uses the production capture implementation unchanged.
//! Build with the scratch Cargo manifest described in perf-repeated-diagnosis.md.
use sha2::{Digest, Sha256};
use std::{
    fs,
    io::{Read, Write},
    path::{Path, PathBuf},
    process::{Command, Stdio},
    time::{Duration, Instant},
};
#[derive(Debug)]
struct Error {
    code: String,
    message: String,
}
impl Error {
    fn new(c: &str, m: impl Into<String>) -> Self {
        Self {
            code: c.into(),
            message: m.into(),
        }
    }
}
impl From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Self {
        Self::new("IO", e.to_string())
    }
}
type Result<T> = std::result::Result<T, Error>;
fn diagnostic(x: std::fmt::Arguments<'_>) {
    eprintln!("{x}")
}
#[path = "../../server/capture.rs"]
mod capture;
fn cmd(exe: &str, threads: &str) -> Command {
    let mut c = Command::new(exe);
    c.env("BENDRTS", "").env("BEND_NO_TELEMETRY", "1").args([
        "+RTS",
        "--threads",
        threads,
        "--gpu",
        "off",
        "-RTS",
    ]);
    c
}
fn files(p: &Path, out: &mut Vec<(PathBuf, Vec<u8>)>) {
    for e in fs::read_dir(p).unwrap() {
        let p = e.unwrap().path();
        if p.is_dir() {
            files(&p, out)
        } else {
            out.push((p.clone(), fs::read(p).unwrap()))
        }
    }
}
fn pool(exe: &str, threads: &str, input: &[u8], pipe_size: i32) -> (u128, Vec<u8>) {
    std::thread::scope(|scope| {
        let (tx, rx) = std::sync::mpsc::sync_channel::<Vec<u8>>(1);
        let mut c = cmd(exe, threads)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        if pipe_size > 0 {
            use std::os::fd::AsRawFd;
            for fd in [
                c.stdin.as_ref().unwrap().as_raw_fd(),
                c.stdout.as_ref().unwrap().as_raw_fd(),
            ] {
                assert!(
                    unsafe { libc::fcntl(fd, libc::F_SETPIPE_SZ, pipe_size) } >= pipe_size,
                    "F_SETPIPE_SZ: {}",
                    std::io::Error::last_os_error()
                );
            }
        }
        let mut sin = c.stdin.take().unwrap();
        let mut sout = c.stdout.take().unwrap();
        let mut serr = c.stderr.take().unwrap();
        let w = scope.spawn(move || {
            sin.write_all(&rx.recv().unwrap()).unwrap();
            drop(sin);
        });
        let r = scope.spawn(move || {
            let mut b = vec![];
            sout.read_to_end(&mut b).unwrap();
            b
        });
        let e = scope.spawn(move || {
            let mut b = vec![];
            serr.read_to_end(&mut b).unwrap();
            b
        });
        let wp = format!("/proc/{}/wchan", c.id());
        let mut ready = false;
        for _ in 0..10000 {
            let x = fs::read_to_string(&wp).unwrap();
            if x.contains("pipe_read") {
                ready = true;
                break;
            }
            std::thread::sleep(Duration::from_micros(50));
        }
        assert!(ready, "child must already be blocked in input read");
        let bytes = input.to_vec();
        let now = Instant::now();
        tx.send(bytes).unwrap();
        assert!(c.wait().unwrap().success());
        w.join().unwrap();
        let out = r.join().unwrap();
        let err = e.join().unwrap();
        let ns = now.elapsed().as_nanos();
        assert!(err.is_empty(), "{:?}", err);
        (ns, out)
    })
}
fn main() {
    let a: Vec<String> = std::env::args().collect();
    let mode = &a[1];
    let mut exe = a[2].clone();
    let input = if mode == "seal" {
        vec![]
    } else {
        fs::read(&a[3]).unwrap()
    };
    let n: usize = a[4].parse().unwrap();
    let threads = &a[5];
    let mut sealed = vec![];
    if mode == "seal" {
        for p in [&a[2], &a[3]] {
            files(Path::new(p), &mut sealed)
        }
    }
    let image = if mode == "hash" {
        fs::read(&exe).unwrap()
    } else {
        vec![]
    };
    let mut memfd = None;
    if mode == "memfd" {
        use std::os::fd::{AsRawFd, FromRawFd};
        use std::os::unix::fs::PermissionsExt;
        let name = std::ffi::CString::new("jaydb-prepared-research").unwrap();
        let fd = unsafe {
            libc::memfd_create(name.as_ptr(), libc::MFD_ALLOW_SEALING | libc::MFD_CLOEXEC)
        };
        assert!(fd >= 0);
        let mut f = unsafe { fs::File::from_raw_fd(fd) };
        f.write_all(&fs::read(&exe).unwrap()).unwrap();
        f.set_permissions(fs::Permissions::from_mode(0o700))
            .unwrap();
        let flags =
            libc::F_SEAL_WRITE | libc::F_SEAL_GROW | libc::F_SEAL_SHRINK | libc::F_SEAL_SEAL;
        assert_eq!(unsafe { libc::fcntl(fd, libc::F_ADD_SEALS, flags) }, 0);
        assert_eq!(unsafe { libc::fcntl(fd, libc::F_GET_SEALS) }, flags);
        assert!(f.write_all(&[0]).is_err());
        exe = format!("/proc/self/fd/{}", f.as_raw_fd());
        memfd = Some(f);
    }
    let mut rows = vec![];
    let mut reference = None;
    let mut output_bytes = 0;
    for i in 0..n + 1 {
        let now = Instant::now();
        let (ns, out) = match mode.as_str() {
            "pool" => pool(&exe, threads, &input, 0),
            "pool-4096" => pool(&exe, threads, &input, 4096),
            "pool-65536" => pool(&exe, threads, &input, 65536),
            "hash" => {
                let b = fs::read(&exe).unwrap();
                std::hint::black_box(Sha256::digest(&b));
                (now.elapsed().as_nanos(), vec![])
            }
            "read-file" => {
                std::hint::black_box(fs::read(&exe).unwrap());
                (now.elapsed().as_nanos(), vec![])
            }
            "hash-memory" => {
                std::hint::black_box(Sha256::digest(&input));
                (now.elapsed().as_nanos(), vec![])
            }
            "seal" => {
                for (p, b) in &sealed {
                    assert!(fs::symlink_metadata(p).unwrap().file_type().is_file());
                    assert_eq!(fs::read(p).unwrap(), *b)
                }
                (now.elapsed().as_nanos(), vec![])
            }
            _ => {
                let out = capture::capture(&mut cmd(&exe, threads), &input).unwrap();
                let ns = now.elapsed().as_nanos();
                assert!(out.status.success(), "{:?}", out.stderr);
                (ns, out.stdout)
            }
        };
        output_bytes = out.len();
        let hash = format!("{:x}", Sha256::digest(&out));
        if let Some(h) = &reference {
            assert_eq!(&hash, h)
        } else {
            reference = Some(hash.clone())
        }
        if i > 0 {
            rows.push(ns)
        }
    }
    println!(
        "{}",
        serde_json::json!({"mode":mode,"exe":a[2],"input":a[3],"input_bytes":input.len(),"output_bytes":output_bytes,"threads":threads,"samples_ns":rows,"output_sha256":reference,"sealed_files":sealed.len(),"executable_bytes":image.len()})
    );
    drop(memfd);
}
