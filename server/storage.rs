//! Two alternating, block-aligned complete-state slots; single directory owner.
//! Routine commits overwrite the older slot and fdatasync the existing inode.
//! Creation/growth use synced temp + atomic rename + directory fsync. Recovery
//! requires checksum-valid complete slots with consecutive, correctly placed
//! sequence numbers (or one valid slot beside an all-zero slot). Nonzero invalid
//! slots stop default recovery without modifying snapshot. Explicit operator
//! repair syncs evidence before clearing a peer and reusing its sequence.
//! Repair may discard an acknowledged commit. Bytes are not a validity proof.
//!
//! Trusted Linux/ext4 boundary: successful fdatasync persists data and required
//! metadata, absent prior writeback errors (see docs/durable-storage.md);
//! directory fsync persists atomic replacement; errors may have effects.
//! Previously synced, unmodified filesystem blocks remain intact across a crash.
//! Slots start/end on 4096-byte filesystem block boundaries. No sector or block
//! write atomicity is assumed. SHA-256 must detect torn/mixed slot contents;
//! undetected collisions are excluded. Protected storage excludes malicious
//! rewriting, unrelated media damage and loss of acknowledged synced writes.
//! Rust/OS refinement and these assumptions remain outside the Bend proofs.
use crate::{Error, Limits, Result};
use sha2::{Digest, Sha256};
use std::fs::{self, DirBuilder, File, OpenOptions};
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt};
use std::path::{Path, PathBuf};

const MAGIC: &[u8] = b"jaydb2-image-v1\n";
const OVERHEAD: usize = MAGIC.len() + 64 + 4 * 8 + 32;
const IMAGE: &str = "snapshot";
const TEMP: &str = ".snapshot.tmp";
const ENVIRONMENT: &str = "environment";
const SLOT_MAGIC: &[u8; 16] = b"jaydb2-slot-v2!!";
const HEADER: usize = 64;
const BLOCK: u64 = 4096;

fn slot_size_for(image_size: u64) -> Option<u64> {
    image_size
        .checked_add(HEADER as u64)?
        .checked_add(BLOCK - 1)
        .map(|n| n / BLOCK * BLOCK)
}

fn encode_slot(sequence: u64, image: &[u8], slot_size: usize) -> io::Result<Vec<u8>> {
    if slot_size_for(image.len() as u64).is_none_or(|n| n > slot_size as u64) {
        return Err(io::Error::other("slot size overflow"));
    }
    let mut record = Vec::with_capacity(slot_size);
    record.extend_from_slice(SLOT_MAGIC);
    record.extend_from_slice(&sequence.to_be_bytes());
    record.extend_from_slice(&(image.len() as u64).to_be_bytes());
    record.resize(HEADER, 0);
    record.extend_from_slice(image);
    // Bind sequence/length TO the payload: a new header with an untouched old
    // payload must never pass as a newer publication after an in-place tear.
    let mut digest = Sha256::new();
    digest.update(&record[..32]);
    digest.update(image);
    record[32..64].copy_from_slice(&digest.finalize());
    record.resize(slot_size, 0);
    Ok(record)
}

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
    pending: Option<File>,
    creating: bool,
    environment_bound: bool,
    sequence: Option<u64>,
    length: u64,
    poisoned: bool,
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
        let mut geometry = std::mem::MaybeUninit::<libc::statvfs>::uninit();
        // SAFETY: live descriptor, writable statvfs output, initialized only
        // after a successful syscall. Only the filesystem block size is read.
        if unsafe { libc::fstatvfs(directory.as_raw_fd(), geometry.as_mut_ptr()) } != 0 {
            return Err(storage_error(io::Error::last_os_error()));
        }
        if unsafe { geometry.assume_init() }.f_frsize != BLOCK {
            return Err(storage_error(
                "storage requires 4096-byte filesystem blocks",
            ));
        }
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
            pending: None,
            creating: mode == Mode::Create,
            environment_bound: false,
            sequence: None,
            length: 0,
            poisoned: false,
        })
    }

    // Bind once, before reading or writing any authoritative image. The
    // immutable descriptor contains exact public source/tooling/controller
    // bytes. Hashes in images remain diagnostics and corruption checks.
    pub fn bind_environment(&mut self, expected: &[u8]) -> Result<()> {
        if self.environment_bound {
            return Err(storage_error("environment already bound"));
        }
        let path = self.path.join(ENVIRONMENT);
        if self.creating {
            let mut file = OpenOptions::new()
                .write(true)
                .create_new(true)
                .mode(0o600)
                .open(path)
                .map_err(storage_error)?;
            file.write_all(expected)
                .and_then(|()| file.sync_all())
                .and_then(|()| self.directory.sync_all())
                .map_err(storage_error)?;
        } else {
            if !fs::symlink_metadata(&path)
                .map_err(storage_error)?
                .file_type()
                .is_file()
            {
                return Err(storage_error(
                    "missing or nonregular exact environment descriptor",
                ));
            }
            let file = File::open(path).map_err(storage_error)?;
            let size = expected.len() as u64;
            if file.metadata().map_err(storage_error)?.len() != size {
                return Err(storage_error(
                    "incompatible image environment (exact descriptor size differs)",
                ));
            }
            let mut actual = Vec::new();
            file.take(size.saturating_add(1))
                .read_to_end(&mut actual)
                .map_err(storage_error)?;
            if actual != expected {
                return Err(storage_error(
                    "incompatible image environment (exact source or controller bytes differ)",
                ));
            }
        }
        self.environment_bound = true;
        Ok(())
    }

    pub fn recover(
        &mut self,
        environment: &str,
        limits: &Limits,
        repair_invalid_slot: bool,
    ) -> Result<Vec<u8>> {
        if !self.environment_bound || self.poisoned {
            return Err(storage_error("environment unbound or storage uncertain"));
        }
        self.poisoned = true;
        let mut file = OpenOptions::new()
            .read(true)
            .write(true)
            .open(self.path.join(IMAGE))
            .map_err(storage_error)?;
        let length = file.metadata().map_err(storage_error)?.len();
        let (state, sequence, repair) =
            decode_slots(&mut file, length, environment, limits, repair_invalid_slot)?;
        if let Some(InvalidSlot { index, bytes }) = repair {
            // Evidence must survive a crash BEFORE the first authoritative write.
            // create_new prevents replacement of any earlier repair evidence.
            self.preserve_invalid_slot(index, &bytes)?;
            fault_point("after_slot_evidence_sync").map_err(storage_error)?;
            // A failed future candidate can retain its valid checksum/header.
            // Reusing those bytes at the same next sequence could resurrect it
            // through a later torn write. Clear an invalid peer DURABLY before
            // admitting another request. Never modify the selected current slot.
            file.seek(SeekFrom::Start(index * (length / 2)))
                .map_err(storage_error)?;
            let zeroes = vec![0; usize::try_from(length / 2).map_err(storage_error)?];
            fault_point("before_slot_clear").map_err(storage_error)?;
            file.write_all(&zeroes[..HEADER + 1])
                .map_err(storage_error)?;
            fault_point("during_slot_clear").map_err(storage_error)?;
            file.write_all(&zeroes[HEADER + 1..])
                .map_err(storage_error)?;
            fault_point("after_slot_clear").map_err(storage_error)?;
        }
        // Stabilize a surviving unsynced slot write/rename
        // before RAM publication or the identical-state optimization.
        file.sync_all().map_err(storage_error)?;
        fault_point("after_recovery_file_sync").map_err(storage_error)?;
        self.directory.sync_all().map_err(storage_error)?;
        fault_point("after_recovery_sync").map_err(storage_error)?;
        self.sequence = Some(sequence);
        self.length = length;
        self.poisoned = false;
        Ok(state)
    }

    fn preserve_invalid_slot(&self, index: u64, bytes: &[u8]) -> Result<()> {
        for serial in 0u64.. {
            let path = self
                .path
                .join(format!("snapshot.invalid-slot-{index}.{serial}.evidence"));
            let mut evidence = match OpenOptions::new()
                .write(true)
                .create_new(true)
                .mode(0o600)
                .open(&path)
            {
                Ok(file) => file,
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
                Err(error) => return Err(storage_error(error)),
            };
            evidence
                .write_all(bytes)
                .and_then(|()| fault_point("before_evidence_file_sync"))
                .and_then(|()| evidence.sync_all())
                .and_then(|()| fault_point("before_evidence_directory_sync"))
                .and_then(|()| self.directory.sync_all())
                .map_err(storage_error)?;
            crate::diagnostic(format_args!(
                "repairing invalid slot {index}; synced evidence {}. This may discard the newest acknowledged commit",
                path.display()
            ));
            return Ok(());
        }
        Err(storage_error("repair evidence names exhausted"))
    }

    pub fn persist(
        &mut self,
        environment: &str,
        limits: &Limits,
        state: &[u8],
    ) -> std::result::Result<(), CommitError> {
        if !self.environment_bound {
            return Err(CommitError {
                uncertain: false,
                cause: io::Error::new(
                    io::ErrorKind::InvalidData,
                    "exact environment descriptor has not been bound",
                ),
            });
        }
        let bytes = encode_image(environment, limits, state).map_err(|cause| CommitError {
            uncertain: false,
            cause,
        })?;
        if self.poisoned || (!self.creating && self.sequence.is_none()) {
            return Err(CommitError {
                uncertain: true,
                cause: io::Error::other("storage requires recovery"),
            });
        }
        let sequence = match self.sequence {
            None => 0,
            Some(n) => n.checked_add(1).ok_or_else(|| CommitError {
                uncertain: false,
                cause: io::Error::other("slot sequence exhausted"),
            })?,
        };
        let needed = slot_size_for(bytes.len() as u64).ok_or_else(|| CommitError {
            uncertain: false,
            cause: io::Error::other("slot size overflow"),
        })?;
        let grow = self.sequence.is_none() || needed > self.length / 2;
        let slot_size = if grow { needed } else { self.length / 2 };
        let slot_size = usize::try_from(slot_size).map_err(|_| CommitError {
            uncertain: false,
            cause: io::Error::other("slot exceeds address space"),
        })?;
        // Padding outside this frame is not authoritative. After a large
        // state shrinks, write/allocate only its currently needed blocks,
        // keeping the original slot geometry and the other slot untouched.
        let record =
            encode_slot(sequence, &bytes, needed as usize).map_err(|cause| CommitError {
                uncertain: false,
                cause,
            })?;
        let result = if grow {
            let total = slot_size.checked_mul(2).ok_or_else(|| CommitError {
                uncertain: false,
                cause: io::Error::other("slot file overflow"),
            })?;
            // Both slots are initialized, allocated and synced at creation or
            // growth. Only one contains a publication; sequence parity fixes it.
            let mut image = vec![0; total];
            let offset = (sequence % 2) as usize * slot_size;
            image[offset..offset + slot_size].copy_from_slice(&record);
            commit(self, &image)
        } else {
            slot_commit(self, &record)
        };
        self.pending = None;
        if result.is_ok() {
            self.sequence = Some(sequence);
            self.length = slot_size as u64 * 2;
        } else if result.as_ref().is_err_and(|e| e.uncertain) {
            self.poisoned = true;
        }
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
        self.pending = Some(file);
        fault_point("after_write")
    }
    fn sync_temp(&mut self) -> io::Result<()> {
        self.pending
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

// Preparation only opens/seeks; the selected older slot is never the latest
// durable publication. Once writing starts every error is conservatively fatal.
trait SlotIo {
    fn prepare_slot(&mut self) -> io::Result<()>;
    fn write_slot(&mut self, record: &[u8]) -> io::Result<()>;
    fn sync_slot(&mut self) -> io::Result<()>;
}

fn slot_commit(io: &mut impl SlotIo, record: &[u8]) -> std::result::Result<(), CommitError> {
    io.prepare_slot().map_err(|cause| CommitError {
        uncertain: false,
        cause,
    })?;
    io.write_slot(record)
        .and_then(|()| io.sync_slot())
        .map_err(|cause| CommitError {
            uncertain: true,
            cause,
        })
}

impl SlotIo for Storage {
    fn prepare_slot(&mut self) -> io::Result<()> {
        fault_point("before_write")?;
        let mut file = OpenOptions::new()
            .read(true)
            .write(true)
            .open(self.path.join(IMAGE))?;
        if file.metadata()?.len() != self.length {
            return Err(io::Error::other("authoritative slot file length changed"));
        }
        let next = self.sequence.expect("recovered slot sequence") + 1;
        file.seek(SeekFrom::Start((next % 2) * (self.length / 2)))?;
        self.pending = Some(file);
        Ok(())
    }
    fn write_slot(&mut self, record: &[u8]) -> io::Result<()> {
        fault_point("before_slot_write")?;
        let file = self.pending.as_mut().expect("prepared slot");
        #[cfg(feature = "storage-fault-injection")]
        {
            // Stop inside the authoritative header/payload, not just padding.
            file.write_all(&record[..HEADER + 1])?;
            fault_point("during_slot_write")?;
            file.write_all(&record[HEADER + 1..])?;
        }
        #[cfg(not(feature = "storage-fault-injection"))]
        file.write_all(record)?;
        fault_point("after_slot_write")
    }
    fn sync_slot(&mut self) -> io::Result<()> {
        fault_point("before_data_sync")?;
        self.pending.as_ref().expect("written slot").sync_data()?;
        fault_point("after_data_sync")
    }
}

fn decode_slot(bytes: &[u8]) -> std::result::Result<(u64, &[u8]), &'static str> {
    if bytes.len() < HEADER || !bytes.starts_with(SLOT_MAGIC) {
        return Err("invalid slot format/magic (expected v2)");
    }
    let size = usize::try_from(u64::from_be_bytes(bytes[24..32].try_into().unwrap()))
        .map_err(|_| "slot image length exceeds address space")?;
    let end = HEADER
        .checked_add(size)
        .ok_or("slot image length overflow")?;
    if size < OVERHEAD || end > bytes.len() {
        return Err("invalid slot image length");
    }
    let mut digest = Sha256::new();
    digest.update(&bytes[..32]);
    digest.update(&bytes[HEADER..end]);
    if digest.finalize()[..] != bytes[32..64] {
        return Err("slot checksum mismatch");
    }
    Ok((
        u64::from_be_bytes(bytes[16..24].try_into().unwrap()),
        &bytes[HEADER..end],
    ))
}

#[derive(Debug)]
struct InvalidSlot {
    index: u64,
    bytes: Vec<u8>,
}

// Shared by OS recovery and arbitrary torn-write tests. Never trusts a length
// before bounding it by actual file geometry and the logical state ceiling.
fn decode_slots(
    file: &mut (impl Read + Seek),
    length: u64,
    environment: &str,
    limits: &Limits,
    repair_invalid_slot: bool,
) -> Result<(Vec<u8>, u64, Option<InvalidSlot>)> {
    if length >= MAGIC.len() as u64 {
        let mut prefix = [0; MAGIC.len()];
        file.read_exact(&mut prefix).map_err(storage_error)?;
        file.seek(SeekFrom::Start(0)).map_err(storage_error)?;
        if prefix.as_slice() == MAGIC {
            return Err(Error::new(
                "STORAGE_FORMAT",
                "unsupported snapshot format v1; expected slot format v2 (explicit recreation required)",
            ));
        }
    }
    let maximum = slot_size_for(limits.state.saturating_add(OVERHEAD as u64)).unwrap_or(u64::MAX);
    if length < BLOCK * 2 || !length.is_multiple_of(BLOCK * 2) || length / 2 > maximum {
        return Err(storage_error(
            "invalid or oversized authoritative slot file",
        ));
    }
    let size = usize::try_from(length / 2).map_err(storage_error)?;
    let mut candidates = Vec::new();
    let mut repair = None;
    for index in 0..2 {
        let mut bytes = vec![0; size];
        file.read_exact(&mut bytes).map_err(storage_error)?;
        if let Ok((sequence, image)) = decode_slot(&bytes) {
            if sequence % 2 != index {
                return Err(storage_error("ambiguous slot sequence placement"));
            }
            // Check every checksum-valid image, including an older one. Never
            // hide an incompatible valid slot behind a newer publication.
            candidates.push((
                sequence,
                decode_image(image, environment, limits).map_err(|error| {
                    Error::new(&error.code, format!("slot {index}: {}", error.message))
                })?,
            ));
        } else if bytes.iter().any(|byte| *byte != 0) {
            let reason = decode_slot(&bytes).unwrap_err();
            if !repair_invalid_slot {
                return Err(Error::new(
                    "STORAGE_INVALID_SLOT",
                    format!(
                        "invalid nonzero slot {index} ({}): {reason}; snapshot unchanged; operator repair requires --repair-invalid-slot and may discard an acknowledged commit",
                        if index == 0 { "A" } else { "B" }
                    ),
                ));
            }
            repair = Some(InvalidSlot { index, bytes });
        }
    }
    candidates.sort_by_key(|(sequence, _)| *sequence);
    if candidates.len() == 2 && candidates[0].0.checked_add(1) != Some(candidates[1].0) {
        return Err(storage_error("ambiguous or stale slot sequences"));
    }
    candidates
        .pop()
        .map(|(sequence, state)| (state, sequence, repair))
        .ok_or_else(|| storage_error("no complete authoritative slot (format or checksum)"))
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

    fn bound_storage(path: &Path, mode: Mode) -> Storage {
        let mut storage = Storage::begin(path, mode).unwrap();
        storage.bind_environment(b"exact test environment").unwrap();
        storage
    }

    #[test]
    fn descriptor_is_required_exact_and_immutable() {
        let parent = Temporary::new(&std::env::temp_dir(), "jaydb-storage-binding").unwrap();
        let path = parent.path.join("db");
        let mut storage = Storage::begin(&path, Mode::Create).unwrap();
        assert!(
            !storage
                .persist(&environment(), &limits(), b"old")
                .unwrap_err()
                .uncertain
        );
        assert!(!path.join(IMAGE).exists());
        storage.bind_environment(b"original environment").unwrap();
        assert!(storage.bind_environment(b"different descriptor").is_err());
        assert_eq!(
            fs::read(path.join(ENVIRONMENT)).unwrap(),
            b"original environment"
        );
        storage.persist(&environment(), &limits(), b"old").unwrap();
        drop(storage);
        let mut storage = Storage::begin(&path, Mode::Open).unwrap();
        assert!(storage.recover(&environment(), &limits(), false).is_err());
        // Same image digest and same-length descriptor still cannot bind
        // changed bytes. No SHA collision-resistance premise is involved.
        assert!(storage.bind_environment(b"changed! environment").is_err());
        assert_eq!(
            fs::read(path.join(ENVIRONMENT)).unwrap(),
            b"original environment"
        );
        storage.bind_environment(b"original environment").unwrap();
        assert_eq!(
            storage.recover(&environment(), &limits(), false).unwrap(),
            b"old"
        );
        drop(storage);
        fs::remove_file(path.join(ENVIRONMENT)).unwrap();
        let mut storage = Storage::begin(&path, Mode::Open).unwrap();
        assert!(storage.bind_environment(b"original environment").is_err());
        assert!(!path.join(ENVIRONMENT).exists());
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
        let mut storage = bound_storage(&path, Mode::Create);
        assert!(Storage::begin(&path, Mode::Create).is_err());
        assert!(Storage::begin(&path, Mode::Open).is_err());
        storage.persist(&environment(), &limits(), b"old").unwrap();
        assert!(Storage::begin(&path, Mode::Open).is_err());
        storage.persist(&environment(), &limits(), b"new").unwrap();
        drop(storage);
        fs::write(path.join(TEMP), b"orphan").unwrap();
        let mut storage = bound_storage(&path, Mode::Open);
        assert_eq!(
            storage.recover(&environment(), &limits(), false).unwrap(),
            b"new"
        );
        fs::write(path.join(IMAGE), b"corrupt").unwrap();
        assert!(storage.recover(&environment(), &limits(), false).is_err());
        fs::remove_file(path.join(IMAGE)).unwrap();
        drop(storage);
        assert!(Storage::begin(&path, Mode::Open).is_err());
        assert!(Storage::begin(&path, Mode::Create).is_err());
    }

    #[test]
    fn largest_logical_limit_still_recovers_a_small_complete_image() {
        let parent = Temporary::new(&std::env::temp_dir(), "jaydb-storage-limit").unwrap();
        let path = parent.path.join("db");
        let mut limits = limits();
        limits.state = u64::MAX;
        let mut storage = bound_storage(&path, Mode::Create);
        storage.persist(&environment(), &limits, b"small").unwrap();
        drop(storage);
        let mut storage = bound_storage(&path, Mode::Open);
        assert_eq!(
            storage.recover(&environment(), &limits, false).unwrap(),
            b"small"
        );
    }

    fn record(n: u64, state: &[u8]) -> Vec<u8> {
        encode_slot(
            n,
            &encode_image(&environment(), &limits(), state).unwrap(),
            BLOCK as usize,
        )
        .unwrap()
    }
    fn read_slots(bytes: &[u8]) -> Result<(Vec<u8>, u64)> {
        decode_slots(
            &mut io::Cursor::new(bytes),
            bytes.len() as u64,
            &environment(),
            &limits(),
            true,
        )
        .map(|(state, sequence, _)| (state, sequence))
    }

    #[test]
    fn every_torn_slot_byte_refuses_or_explicitly_recovers_old_or_new_and_never_stale() {
        // Current sequence 1 lives in B; A still has sequence 0. Sequence 2
        // overwrites A. New header + fully old body MUST fail the combined hash.
        let stale = record(0, b"stale");
        let old = record(1, b"old");
        let new = record(2, b"new");
        for cut in 0..=new.len() {
            let mut torn = stale.clone();
            torn[..cut].copy_from_slice(&new[..cut]);
            let bytes = [torn.clone(), old.clone()].concat();
            let strict = decode_slots(
                &mut io::Cursor::new(&bytes),
                bytes.len() as u64,
                &environment(),
                &limits(),
                false,
            );
            if decode_slot(&torn).is_err() {
                assert_eq!(
                    strict.unwrap_err().code,
                    "STORAGE_INVALID_SLOT",
                    "cut {cut}"
                );
            } else {
                assert!(strict.is_ok(), "cut {cut}");
            }
            let (state, seq) = read_slots(&bytes).unwrap();
            assert!(state == b"old" || state == b"new", "cut {cut}");
            assert!(seq == 1 || seq == 2);
        }
        let mut mixed = stale;
        mixed[..HEADER].copy_from_slice(&new[..HEADER]);
        assert_eq!(
            read_slots(&[mixed, old.clone()].concat()).unwrap().0,
            b"old"
        );
        for i in 0..new.len() {
            let mut torn = new.clone();
            torn[i] ^= 1;
            let (state, _) = read_slots(&[torn, old.clone()].concat()).unwrap();
            assert!(state == b"old" || state == b"new");
        }
        for cut in 0..old.len() * 2 {
            assert!(read_slots(&[new.clone(), old.clone()].concat()[..cut]).is_err());
        }
    }

    #[test]
    fn explicit_repair_handles_torn_sector_and_block_subsets() {
        let mut large = limits();
        large.state = 16384;
        let slot_size = 12288;
        let image = |n, state: &[u8]| {
            encode_slot(
                n,
                &encode_image(&environment(), &large, state).unwrap(),
                slot_size,
            )
            .unwrap()
        };
        let stale = image(0, &vec![11; 10000]);
        let old = image(1, b"old");
        let state = vec![123; 10000];
        let new = image(2, &state);
        let check = |torn: Vec<u8>| {
            let bytes = [torn, old.clone()].concat();
            let (got, _, _) = decode_slots(
                &mut io::Cursor::new(&bytes),
                bytes.len() as u64,
                &environment(),
                &large,
                true,
            )
            .unwrap();
            assert!(got == b"old" || got == state);
        };
        for mask in 0..(1 << (slot_size / 4096)) {
            let mut torn = stale.clone();
            for (i, chunk) in new.chunks(4096).enumerate() {
                if mask & (1 << i) != 0 {
                    torn[i * 4096..(i + 1) * 4096].copy_from_slice(chunk);
                }
            }
            check(torn);
        }
        for i in 0..slot_size / 512 {
            let mut only = stale.clone();
            only[i * 512..(i + 1) * 512].copy_from_slice(&new[i * 512..(i + 1) * 512]);
            check(only);
            let mut missing = new.clone();
            missing[i * 512..(i + 1) * 512].copy_from_slice(&stale[i * 512..(i + 1) * 512]);
            check(missing);
        }
    }

    #[test]
    fn recovery_refuses_stale_tied_misplaced_and_incompatible_slots() {
        for n in [0, 1, 3, 6, u64::MAX] {
            assert!(read_slots(&[record(n, b"bad"), record(3, b"old")].concat()).is_err());
        }
        let other = encode_image(&"b".repeat(64), &limits(), b"bad").unwrap();
        assert!(
            read_slots(&[encode_slot(2, &other, 4096).unwrap(), record(3, b"old")].concat())
                .is_err()
        );
        let mut other_limits = limits();
        other_limits.message += 1;
        let other = encode_image(&environment(), &other_limits, b"bad").unwrap();
        assert!(
            read_slots(&[encode_slot(2, &other, 4096).unwrap(), record(3, b"old")].concat())
                .is_err()
        );
        assert!(read_slots(&[vec![0; 4096], vec![0; 4096]].concat()).is_err());
        assert!(read_slots(&vec![0; 4096 * 4]).is_err());
        assert_eq!(
            read_slots(&[record(2, b"new"), record(1, b"old")].concat())
                .unwrap()
                .0,
            b"new"
        );
        assert_eq!(
            read_slots(&[vec![0; 4096], record(u64::MAX, b"last")].concat())
                .unwrap()
                .1,
            u64::MAX
        );
    }

    #[test]
    fn corrupt_acknowledged_slot_is_untouched_by_default_and_repair_preserves_evidence() {
        for index in 0..2 {
            let parent = Temporary::new(&std::env::temp_dir(), "jaydb-corrupt-slot").unwrap();
            let path = parent.path.join("db");
            let mut storage = bound_storage(&path, Mode::Create);
            storage.persist(&environment(), &limits(), b"seed").unwrap();
            storage.persist(&environment(), &limits(), b"old").unwrap();
            if index == 0 {
                storage.persist(&environment(), &limits(), b"new").unwrap();
            }
            drop(storage);
            let mut corrupt = fs::read(path.join(IMAGE)).unwrap();
            corrupt[index * BLOCK as usize + HEADER + OVERHEAD] ^= 1;
            fs::write(path.join(IMAGE), &corrupt).unwrap();
            let mut storage = bound_storage(&path, Mode::Open);
            let error = storage
                .recover(&environment(), &limits(), false)
                .unwrap_err();
            assert_eq!(error.code, "STORAGE_INVALID_SLOT");
            assert!(error.message.contains(&format!("slot {index}")));
            assert!(error.message.contains("checksum"));
            assert_eq!(fs::read(path.join(IMAGE)).unwrap(), corrupt);
            assert_eq!(fs::read_dir(&path).unwrap().count(), 3);
            drop(storage);
            // Existing evidence is never overwritten, including interrupted copies.
            let evidence = path.join(format!("snapshot.invalid-slot-{index}.0.evidence"));
            fs::write(&evidence, b"earlier evidence").unwrap();
            let mut storage = bound_storage(&path, Mode::Open);
            let state = storage.recover(&environment(), &limits(), true).unwrap();
            assert_eq!(
                state,
                if index == 0 {
                    b"old".as_slice()
                } else {
                    b"seed".as_slice()
                }
            );
            assert_eq!(fs::read(&evidence).unwrap(), b"earlier evidence");
            let saved =
                fs::read(path.join(format!("snapshot.invalid-slot-{index}.1.evidence"))).unwrap();
            assert_eq!(
                saved,
                corrupt[index * BLOCK as usize..(index + 1) * BLOCK as usize]
            );
            let repaired = fs::read(path.join(IMAGE)).unwrap();
            assert!(
                repaired[index * BLOCK as usize..(index + 1) * BLOCK as usize]
                    .iter()
                    .all(|b| *b == 0)
            );
            assert_eq!(
                repaired[(1 - index) * BLOCK as usize..(2 - index) * BLOCK as usize],
                corrupt[(1 - index) * BLOCK as usize..(2 - index) * BLOCK as usize]
            );
        }
    }

    #[test]
    fn old_v1_snapshot_fails_closed_without_any_byte_changes_even_with_repair() {
        let parent = Temporary::new(&std::env::temp_dir(), "jaydb-v1").unwrap();
        let path = parent.path.join("db");
        let mut storage = bound_storage(&path, Mode::Create);
        storage.persist(&environment(), &limits(), b"seed").unwrap();
        drop(storage);
        let old_image = encode_image(&environment(), &limits(), b"old v1 state").unwrap();
        fs::write(path.join(IMAGE), &old_image).unwrap();
        for repair in [false, true] {
            let mut storage = bound_storage(&path, Mode::Open);
            let error = storage
                .recover(&environment(), &limits(), repair)
                .unwrap_err();
            assert_eq!(error.code, "STORAGE_FORMAT");
            assert!(error.message.contains("format v1"));
            assert_eq!(fs::read(path.join(IMAGE)).unwrap(), old_image);
            assert_eq!(fs::read_dir(&path).unwrap().count(), 3);
        }
    }

    #[test]
    fn real_slots_survive_repeated_overwrites_growth_and_restart() {
        use std::os::unix::fs::MetadataExt;
        let parent = Temporary::new(&std::env::temp_dir(), "jaydb-slots").unwrap();
        let path = parent.path.join("db");
        let mut large = limits();
        large.state = 16384;
        let mut storage = bound_storage(&path, Mode::Create);
        storage.persist(&environment(), &large, b"old").unwrap();
        let live = File::open(path.join(IMAGE)).unwrap();
        let inode = live.metadata().unwrap().ino();
        for n in 1..=64 {
            storage
                .persist(&environment(), &large, n.to_string().as_bytes())
                .unwrap();
            assert_eq!(fs::metadata(path.join(IMAGE)).unwrap().ino(), inode);
            assert_eq!(storage.length, 8192);
        }
        let state = vec![12; 9000];
        storage.persist(&environment(), &large, &state).unwrap();
        assert_ne!(fs::metadata(path.join(IMAGE)).unwrap().ino(), inode);
        assert_eq!(storage.length, 24576);
        assert_eq!(storage.sequence, Some(65));
        drop(storage);
        let mut storage = bound_storage(&path, Mode::Open);
        assert_eq!(
            storage.recover(&environment(), &large, false).unwrap(),
            state
        );
        storage.persist(&environment(), &large, b"small").unwrap();
        assert_eq!(storage.length, 24576); // never shrinks/aliases the latest slot
        assert_eq!(
            storage.recover(&environment(), &large, false).unwrap(),
            b"small"
        );
        storage.persist(&environment(), &large, b"tiny").unwrap();
        assert_eq!(fs::read(path.join(IMAGE)).unwrap()[12288 + 5000], 12);
        assert_eq!(
            storage.recover(&environment(), &large, false).unwrap(),
            b"tiny"
        );
        assert!(
            !storage
                .persist(&environment(), &large, &vec![0; large.state as usize + 1])
                .unwrap_err()
                .uncertain
        );
        assert_eq!(
            storage.recover(&environment(), &large, false).unwrap(),
            b"tiny"
        );
        storage.sequence = Some(u64::MAX);
        assert!(
            !storage
                .persist(&environment(), &large, b"next")
                .unwrap_err()
                .uncertain
        );
        storage.poisoned = true;
        assert!(
            storage
                .persist(&environment(), &large, b"next")
                .unwrap_err()
                .uncertain
        );
        assert!(storage.recover(&environment(), &large, false).is_err());
    }

    #[test]
    fn recovery_clears_failed_future_slot_before_reusing_its_sequence() {
        let parent = Temporary::new(&std::env::temp_dir(), "jaydb-slot-clear").unwrap();
        let path = parent.path.join("db");
        let mut storage = bound_storage(&path, Mode::Create);
        storage.persist(&environment(), &limits(), b"seed").unwrap();
        storage.persist(&environment(), &limits(), b"old").unwrap();
        drop(storage);
        let failed_state = vec![0; 900];
        let failed = record(2, &failed_state);
        let mut invalid = failed.clone();
        let missing = HEADER + MAGIC.len() + 64 + 32 + 600;
        invalid[missing] ^= 128;
        assert!(decode_slot(&invalid).is_err());
        // An out-of-order partial zeroing can itself resurrect that earlier
        // candidate before repair sync. Startup has admitted no request yet.
        let mut partial_clear = invalid.clone();
        partial_clear[512..1024].fill(0);
        assert_eq!(
            read_slots(&[partial_clear, record(1, b"old")].concat())
                .unwrap()
                .0,
            failed_state
        );
        let mut file = OpenOptions::new()
            .write(true)
            .open(path.join(IMAGE))
            .unwrap();
        file.write_all(&invalid).unwrap();
        drop(file);
        let mut storage = bound_storage(&path, Mode::Open);
        assert_eq!(
            storage.recover(&environment(), &limits(), true).unwrap(),
            b"old"
        );
        assert!(
            fs::read(path.join(IMAGE)).unwrap()[..BLOCK as usize]
                .iter()
                .all(|b| *b == 0)
        );
        // Without clearing, a later torn write restoring just the missing byte
        // resurrects the failed future candidate under the SAME next sequence.
        invalid[missing] = failed[missing];
        assert_eq!(
            read_slots(&[invalid, record(1, b"old")].concat())
                .unwrap()
                .0,
            failed_state
        );
        // After durable clearing, every next-write prefix can recover only the
        // current publication or THIS candidate, never the earlier failed one.
        let next = record(2, b"different");
        for cut in 0..=next.len() {
            let mut torn = vec![0; next.len()];
            torn[..cut].copy_from_slice(&next[..cut]);
            let state = read_slots(&[torn, record(1, b"old")].concat()).unwrap().0;
            assert!(state == b"old" || state == b"different");
        }
        storage
            .persist(&environment(), &limits(), b"different")
            .unwrap();
        assert_eq!(
            storage.recover(&environment(), &limits(), true).unwrap(),
            b"different"
        );
    }

    struct SlotModel {
        stage: usize,
        fail: usize,
        after: bool,
        written: bool,
        synced: bool,
    }
    impl SlotModel {
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
    }
    impl SlotIo for SlotModel {
        fn prepare_slot(&mut self) -> io::Result<()> {
            self.step(|_| {})
        }
        fn write_slot(&mut self, _: &[u8]) -> io::Result<()> {
            self.step(|m| m.written = true)
        }
        fn sync_slot(&mut self) -> io::Result<()> {
            self.step(|m| {
                assert!(m.written);
                m.synced = true;
            })
        }
    }
    #[test]
    fn actual_slot_algorithm_covers_every_fault_and_crash_boundary() {
        for fail in 0..=3 {
            for after in [false, true] {
                let mut m = SlotModel {
                    stage: 0,
                    fail,
                    after,
                    written: false,
                    synced: false,
                };
                let result = slot_commit(&mut m, b"new");
                if fail == 0 {
                    assert!(result.is_ok());
                    assert!(m.synced);
                } else {
                    assert_eq!(result.unwrap_err().uncertain, fail >= 2);
                }
                for survives in [false, true] {
                    let recovered = if m.synced || (m.written && survives) {
                        b"new"
                    } else {
                        b"old"
                    };
                    if fail == 0 {
                        assert_eq!(recovered, b"new");
                    }
                    if fail == 1 {
                        assert_eq!(recovered, b"old");
                    }
                    assert!(recovered == b"old" || recovered == b"new");
                }
            }
        }
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
