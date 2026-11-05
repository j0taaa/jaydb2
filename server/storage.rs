//! One authoritative complete image, with a single directory owner.
//! Storage bytes are not a validity proof. See experiments/persistence/REPORT.md.
use crate::{Error, Limits, Result};
use sha2::{Digest, Sha256};
use std::fs::{self, DirBuilder, File, OpenOptions};
use std::io::{self, Read, Write};
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt};
use std::path::{Path, PathBuf};

const MAGIC: &[u8] = b"jaydb2-image-v1\n";
const OVERHEAD: usize = MAGIC.len() + 64 + 4 * 8 + 32;
const IMAGE: &str = "snapshot";
const TEMP: &str = ".snapshot.tmp";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    Create,
    Open,
}

pub struct Storage {
    path: PathBuf,
    directory: File,
    // Never unlink or replace this file: its locked inode identifies ownership.
    _owner: File,
    temporary: Option<File>,
}

#[derive(Debug)]
pub struct CommitError {
    pub uncertain: bool,
    pub cause: io::Error,
}

impl From<CommitError> for Error {
    fn from(error: CommitError) -> Self {
        Self::new(
            if error.uncertain {
                "STORAGE_UNCERTAIN"
            } else {
                "STORAGE_IO"
            },
            error.cause.to_string(),
        )
    }
}

// This is the actual commit algorithm, used by both the OS and the fault model.
// Replacement may have happened even if replace() returns an error. From that
// call onward no failure may be reported as an ordinary rolled-back request.
trait ImageIo {
    fn write_temp(&mut self, image: &[u8]) -> io::Result<()>;
    fn sync_temp(&mut self) -> io::Result<()>;
    fn replace(&mut self) -> io::Result<()>;
    fn sync_directory(&mut self) -> io::Result<()>;
}

fn commit(io: &mut impl ImageIo, image: &[u8]) -> std::result::Result<(), CommitError> {
    io.write_temp(image)
        .and_then(|()| io.sync_temp())
        .map_err(|cause| CommitError {
            uncertain: false,
            cause,
        })?;
    io.replace()
        .and_then(|()| io.sync_directory())
        .map_err(|cause| CommitError {
            uncertain: true,
            cause,
        })
}

fn storage_error(error: impl std::fmt::Display) -> Error {
    Error::new("STORAGE", error.to_string())
}

impl Storage {
    pub fn begin(path: &Path, mode: Mode) -> Result<Self> {
        if mode == Mode::Create {
            // An existing, empty or interrupted directory is never reseeded.
            DirBuilder::new()
                .mode(0o700)
                .create(path)
                .map_err(storage_error)?;
            let parent = path
                .parent()
                .filter(|p| !p.as_os_str().is_empty())
                .unwrap_or(Path::new("."));
            File::open(parent)
                .and_then(|file| file.sync_all())
                .map_err(storage_error)?;
        }
        if !fs::symlink_metadata(path)
            .map_err(storage_error)?
            .file_type()
            .is_dir()
        {
            return Err(storage_error("storage must be a real directory"));
        }
        let owner_path = path.join("owner.lock");
        if mode == Mode::Open
            && !fs::symlink_metadata(&owner_path)
                .map_err(storage_error)?
                .file_type()
                .is_file()
        {
            return Err(storage_error("missing or nonregular owner.lock"));
        }
        let owner = OpenOptions::new()
            .read(true)
            .write(true)
            .create_new(mode == Mode::Create)
            .mode(0o600)
            .open(owner_path)
            .map_err(storage_error)?;
        owner.try_lock().map_err(storage_error)?;
        let directory = File::open(path).map_err(storage_error)?;
        if mode == Mode::Create {
            owner
                .sync_all()
                .and_then(|()| directory.sync_all())
                .map_err(storage_error)?;
        } else if !fs::symlink_metadata(path.join(IMAGE))
            .map_err(storage_error)?
            .file_type()
            .is_file()
        {
            return Err(storage_error(
                "missing or nonregular authoritative snapshot",
            ));
        }
        Ok(Self {
            path: path.to_owned(),
            directory,
            _owner: owner,
            temporary: None,
        })
    }

    pub fn recover(&self, environment: &str, limits: &Limits) -> Result<Vec<u8>> {
        // Bound allocation before reading untrusted/corrupt lengths. There is
        // exactly one candidate; a leftover temp image is never recovery input.
        let maximum = limits
            .state
            .checked_add(OVERHEAD as u64)
            .ok_or_else(|| storage_error("image size overflow"))?;
        let file = File::open(self.path.join(IMAGE)).map_err(storage_error)?;
        if file.metadata().map_err(storage_error)?.len() > maximum {
            return Err(storage_error("oversized authoritative snapshot"));
        }
        let mut bytes = Vec::new();
        file.take(maximum.saturating_add(1))
            .read_to_end(&mut bytes)
            .map_err(storage_error)?;
        decode_image(&bytes, environment, limits)
    }

    pub fn persist(
        &mut self,
        environment: &str,
        limits: &Limits,
        state: &[u8],
    ) -> std::result::Result<(), CommitError> {
        let bytes = encode_image(environment, limits, state).map_err(|cause| CommitError {
            uncertain: false,
            cause,
        })?;
        let result = commit(self, &bytes);
        // Closing the already synced file requires no further rollback-capable
        // work. A failed temp is removable before the next attempt, under lock.
        self.temporary = None;
        result
    }
}

impl ImageIo for Storage {
    fn write_temp(&mut self, image: &[u8]) -> io::Result<()> {
        fault_point("before_write")?;
        match fs::remove_file(self.path.join(TEMP)) {
            Ok(()) => (),
            Err(error) if error.kind() == io::ErrorKind::NotFound => (),
            Err(error) => return Err(error),
        }
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(self.path.join(TEMP))?;
        file.write_all(image)?;
        self.temporary = Some(file);
        fault_point("after_write")
    }
    fn sync_temp(&mut self) -> io::Result<()> {
        self.temporary
            .as_ref()
            .expect("written temporary image")
            .sync_all()?;
        fault_point("after_file_sync")
    }
    fn replace(&mut self) -> io::Result<()> {
        fault_point("before_replace")?;
        fs::rename(self.path.join(TEMP), self.path.join(IMAGE))?;
        fault_point("after_replace")
    }
    fn sync_directory(&mut self) -> io::Result<()> {
        self.directory.sync_all()?;
        fault_point("after_directory_sync")
    }
}

fn encode_image(environment: &str, limits: &Limits, state: &[u8]) -> io::Result<Vec<u8>> {
    if environment.len() != 64
        || !environment.bytes().all(|b| b.is_ascii_hexdigit())
        || state.len() as u64 > limits.state
    {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "invalid image binding or state size",
        ));
    }
    let mut bytes = Vec::with_capacity(OVERHEAD + state.len());
    bytes.extend_from_slice(MAGIC);
    bytes.extend_from_slice(environment.as_bytes());
    for n in [
        limits.message,
        limits.state,
        limits.response,
        state.len() as u64,
    ] {
        bytes.extend_from_slice(&n.to_be_bytes());
    }
    bytes.extend_from_slice(state);
    bytes.extend_from_slice(&Sha256::digest(&bytes));
    Ok(bytes)
}

fn decode_image(bytes: &[u8], environment: &str, limits: &Limits) -> Result<Vec<u8>> {
    if bytes.len() < OVERHEAD || !bytes.starts_with(MAGIC) {
        return Err(storage_error("invalid image format"));
    }
    let end = bytes.len() - 32;
    if Sha256::digest(&bytes[..end])[..] != bytes[end..] {
        return Err(storage_error("image checksum mismatch"));
    }
    let mut offset = MAGIC.len();
    if bytes[offset..offset + 64] != *environment.as_bytes() {
        return Err(storage_error(
            "incompatible image environment (requires the same executable and configuration)",
        ));
    }
    offset += 64;
    for expected in [
        limits.message,
        limits.state,
        limits.response,
        (bytes.len() - OVERHEAD) as u64,
    ] {
        let n = u64::from_be_bytes(bytes[offset..offset + 8].try_into().unwrap());
        if n != expected {
            return Err(storage_error("image limits or length mismatch"));
        }
        offset += 8;
    }
    if (end - offset) as u64 > limits.state {
        return Err(storage_error("image state limit"));
    }
    Ok(bytes[offset..end].to_vec())
}

// Not compiled into production. Tests arm the hook only after initialization.
// A Unix socket supplies a deterministic boundary without timing races.
pub fn fault_point(point: &str) -> io::Result<()> {
    #[cfg(feature = "storage-fault-injection")]
    if std::env::var("JAYDB_STORAGE_FAULT").as_deref() == Ok(point) {
        if let Ok(socket) = std::env::var("JAYDB_STORAGE_BARRIER") {
            let mut stream = std::os::unix::net::UnixStream::connect(socket)?;
            stream.write_all(point.as_bytes())?;
            stream.read_exact(&mut [0])?;
        }
        return Err(io::Error::from_raw_os_error(5)); // EIO
    }
    let _ = point;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Temporary;

    fn limits() -> Limits {
        Limits {
            message: 100,
            state: 1000,
            response: 100,
        }
    }
    fn environment() -> String {
        "a".repeat(64)
    }

    #[test]
    fn image_is_exact_bound_and_fail_closed() {
        let state: Vec<_> = (0..=255).collect();
        let image = encode_image(&environment(), &limits(), &state).unwrap();
        assert_eq!(
            decode_image(&image, &environment(), &limits()).unwrap(),
            state
        );
        assert!(decode_image(&image, &"b".repeat(64), &limits()).is_err());
        let mut other = limits();
        other.message += 1;
        assert!(decode_image(&image, &environment(), &other).is_err());
        for i in 0..image.len() {
            let mut corrupt = image.clone();
            corrupt[i] ^= 1;
            assert!(decode_image(&corrupt, &environment(), &limits()).is_err());
            assert!(decode_image(&image[..i], &environment(), &limits()).is_err());
        }
        let mut extended = image;
        extended.push(0);
        assert!(decode_image(&extended, &environment(), &limits()).is_err());
    }

    #[test]
    fn real_storage_owns_and_recovers_only_authoritative_image() {
        let parent = Temporary::new(&std::env::temp_dir(), "jaydb-storage").unwrap();
        let path = parent.path.join("db");
        assert!(Storage::begin(&path, Mode::Open).is_err());
        let mut storage = Storage::begin(&path, Mode::Create).unwrap();
        assert!(Storage::begin(&path, Mode::Create).is_err());
        assert!(Storage::begin(&path, Mode::Open).is_err());
        storage.persist(&environment(), &limits(), b"old").unwrap();
        assert!(Storage::begin(&path, Mode::Open).is_err());
        storage.persist(&environment(), &limits(), b"new").unwrap();
        drop(storage);
        fs::write(path.join(TEMP), b"orphan").unwrap();
        let storage = Storage::begin(&path, Mode::Open).unwrap();
        assert_eq!(storage.recover(&environment(), &limits()).unwrap(), b"new");
        fs::write(path.join(IMAGE), b"corrupt").unwrap();
        assert!(storage.recover(&environment(), &limits()).is_err());
        fs::remove_file(path.join(IMAGE)).unwrap();
        drop(storage);
        assert!(Storage::begin(&path, Mode::Open).is_err());
        assert!(Storage::begin(&path, Mode::Create).is_err());
    }

    // A deliberately small power-loss model: file data is persistent after
    // file sync; a rename before directory sync can recover old OR new. A torn
    // temp never becomes authoritative. Errors can occur before/after effects.
    struct Model {
        stage: usize,
        fail: usize,
        after: bool,
        temp: Vec<u8>,
        synced: bool,
        replaced: bool,
        directory_synced: bool,
    }
    impl Model {
        fn step(&mut self, effect: impl FnOnce(&mut Self)) -> io::Result<()> {
            self.stage += 1;
            if self.stage == self.fail && !self.after {
                return Err(io::Error::from_raw_os_error(28));
            }
            effect(self);
            if self.stage == self.fail {
                return Err(io::Error::from_raw_os_error(5));
            }
            Ok(())
        }
        fn crash_images(&self) -> Vec<&[u8]> {
            if self.directory_synced {
                vec![&self.temp]
            } else if self.replaced {
                vec![b"old", &self.temp]
            } else {
                vec![b"old"]
            }
        }
    }
    impl ImageIo for Model {
        fn write_temp(&mut self, image: &[u8]) -> io::Result<()> {
            self.step(|m| m.temp = image.to_vec())
        }
        fn sync_temp(&mut self) -> io::Result<()> {
            self.step(|m| m.synced = true)
        }
        fn replace(&mut self) -> io::Result<()> {
            self.step(|m| {
                assert!(m.synced);
                m.replaced = true;
            })
        }
        fn sync_directory(&mut self) -> io::Result<()> {
            self.step(|m| m.directory_synced = true)
        }
    }

    #[test]
    fn actual_commit_algorithm_covers_every_fault_and_crash_boundary() {
        for fail in 0..=4 {
            for after in [false, true] {
                let mut m = Model {
                    stage: 0,
                    fail,
                    after,
                    temp: vec![],
                    synced: false,
                    replaced: false,
                    directory_synced: false,
                };
                let result = commit(&mut m, b"new");
                if fail == 0 {
                    assert!(result.is_ok());
                    assert_eq!(m.crash_images(), [b"new".as_slice()]);
                } else {
                    let error = result.unwrap_err();
                    assert_eq!(error.uncertain, fail >= 3);
                    if !error.uncertain {
                        assert_eq!(m.crash_images(), [b"old".as_slice()]);
                    }
                    for recovered in m.crash_images() {
                        assert!(recovered == b"old" || recovered == b"new");
                    }
                }
            }
        }
    }
}
