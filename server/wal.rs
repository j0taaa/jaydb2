//! Live engine write-ahead log, checkpoints and recovery. See docs/live-engine.md.
#![allow(dead_code)]

use crate::storage::fault_point;
use sha2::{Digest, Sha256};
use std::fs::{self, DirBuilder, File, OpenOptions};
use std::io::{self, Read, Write};
use std::os::unix::fs::{DirBuilderExt, FileExt, OpenOptionsExt};
use std::path::{Path, PathBuf};
use std::sync::Mutex;

const SEGMENT_SIZE: u64 = 8 * 1024 * 1024;
/// Callers split larger groups into several frames, each synced in order.
pub const FRAME_TARGET: usize = 4 * 1024 * 1024;
const CHECKPOINT_MAGIC: &[u8] = b"jaydb2-wal-checkpoint-v2\n";
const CHECKPOINT_TEMP: &str = ".checkpoint.tmp";
const OWNER: &str = "owner.lock";
const SALT: usize = 16;
const SEGMENT_MAGIC: &[u8] = b"jaydb2-wal-segment-v2\n";
/// Magic, salt, first LSN, CRC-32 of the preceding fields.
const SEGMENT_HEADER: usize = SEGMENT_MAGIC.len() + SALT + 8 + 4;
const FRAME_TAG: &[u8] = b"jaydb2-wal-frame-v2\0";
/// Body length (u64), body CRC-32, salted tag of the two (8 bytes).
const FRAME_HEADER: usize = 8 + 4 + 8;
const RECORD_HEADER: usize = 8 + 1; // LSN, kind
const MIN_BODY: usize = RECORD_HEADER + 8; // A commit with no writes.
const MIN_FRAME: usize = FRAME_HEADER + MIN_BODY;
const MIN_WRITE: usize = 1 + 8 + 1;
const COMMIT: u8 = 1;
const EPOCH: u8 = 2;

/// Random per-log value in every checkpoint and segment header. Frame tags
/// include it, so bytes inside user rows cannot form a frame that verifies.
type Salt = [u8; SALT];

#[derive(Debug, PartialEq, Eq)]
pub struct WriteEntry {
    pub collection: Option<String>,
    pub key: String,
    pub row: Option<Vec<u8>>,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Record {
    Commit {
        lsn: u64,
        writes: Vec<WriteEntry>,
    },
    Epoch {
        lsn: u64,
        descriptor: Vec<u8>,
        state: Vec<u8>,
    },
}

impl Record {
    fn lsn(&self) -> u64 {
        match self {
            Self::Commit { lsn, .. } | Self::Epoch { lsn, .. } => *lsn,
        }
    }

    /// Bytes this record adds to a frame body (approximate for epochs under
    /// storage-fault-injection, which rebinds the descriptor).
    pub fn encoded_len(&self) -> usize {
        let optional = |value: Option<usize>| 1 + value.map_or(0, |len| 8 + len);
        RECORD_HEADER
            + match self {
                Self::Commit { writes, .. } => {
                    8 + writes
                        .iter()
                        .map(|write| {
                            optional(write.collection.as_ref().map(String::len))
                                + 8
                                + write.key.len()
                                + optional(write.row.as_ref().map(Vec::len))
                        })
                        .sum::<usize>()
                }
                Self::Epoch {
                    descriptor, state, ..
                } => 8 + descriptor.len() + 8 + state.len(),
            }
    }
}

#[derive(Debug)]
pub struct Recovered {
    /// Last recovered record or checkpoint LSN.
    pub lsn: u64,
    pub descriptor: Vec<u8>,
    /// State from the checkpoint or the last epoch after it.
    pub state: Vec<u8>,
    /// Commits after the state above, in replay order.
    pub commits: Vec<(u64, Vec<WriteEntry>)>,
}

pub struct Log {
    path: PathBuf,
    directory: File,
    salt: Salt,
    // Only checkpoint callers take this lock. They take writer briefly before
    // writing the snapshot and again after its directory entry is durable.
    checkpoints: Mutex<Checkpoints>,
    writer: Mutex<Writer>,
    _owner: Owner,
}

struct Owner(File);

impl Owner {
    fn lock(file: File) -> io::Result<Self> {
        file.try_lock()?;
        Ok(Self(file))
    }
}

impl Drop for Owner {
    fn drop(&mut self) {
        // A concurrent fork can hold the same open file description until
        // exec. Release the lock when the host drops ownership.
        let _ = self.0.unlock();
    }
}

struct Checkpoints {
    latest: u64,
    oldest: u64,
}

struct Writer {
    lsn: u64,
    failed: bool,
    active: Option<Segment>,
    // First and last LSNs, in segment order.
    closed: Vec<(u64, u64)>,
}

struct Segment {
    first: u64,
    bytes: u64,
    capacity: u64,
    file: File,
}

impl Log {
    pub fn create(path: &Path, descriptor: &[u8], initial_state: &[u8]) -> io::Result<Self> {
        match DirBuilder::new().mode(0o700).create(path) {
            Ok(()) => (),
            Err(error) if error.kind() == io::ErrorKind::AlreadyExists => (),
            Err(error) => return Err(error),
        }
        let directory = open_directory(path)?;
        if fs::read_dir(path)?.next().transpose()?.is_some() {
            return Err(input_error("WAL directory must be empty"));
        }
        let owner = Owner::lock(new_file(&path.join(OWNER))?)?;
        owner.0.sync_all()?;
        let parent = path
            .parent()
            .filter(|parent| !parent.as_os_str().is_empty())
            .unwrap_or(Path::new("."));
        File::open(parent)?.sync_all()?;
        let mut salt = [0; SALT];
        File::open("/dev/urandom")?.read_exact(&mut salt)?;
        let log = Self {
            path: path.to_owned(),
            directory,
            salt,
            _owner: owner,
            checkpoints: Mutex::new(Checkpoints {
                latest: 0,
                oldest: 0,
            }),
            writer: Mutex::new(Writer {
                lsn: 0,
                failed: false,
                active: None,
                closed: Vec::new(),
            }),
        };
        log.write_checkpoint(0, descriptor, initial_state)?;
        #[cfg(feature = "storage-fault-injection")]
        power_loss::start(path, salt)?;
        Ok(log)
    }

    pub fn open(path: &Path, expected_descriptor: &[u8]) -> io::Result<(Self, Recovered)> {
        let directory = open_directory(path)?;
        let owner_path = path.join(OWNER);
        require_file(&owner_path)?;
        let owner = Owner::lock(OpenOptions::new().read(true).write(true).open(owner_path)?)?;

        let mut checkpoints = numbered_files(path, "checkpoint-")?;
        let newest_checkpoint = checkpoints
            .last()
            .copied()
            .ok_or_else(|| invalid("WAL has no checkpoint"))?;
        let recovered = loop {
            let lsn = checkpoints
                .pop()
                .ok_or_else(|| invalid("WAL has no valid checkpoint"))?;
            let bytes = fs::read(checkpoint_path(path, lsn))?;
            if let Some(found) = decode_checkpoint(&bytes, lsn) {
                break found;
            }
        };
        let (salt, mut recovered) = recovered;
        let checkpoint_lsn = recovered.lsn;
        let mut writer = Writer {
            lsn: checkpoint_lsn,
            failed: false,
            active: None,
            closed: Vec::new(),
        };
        let segments = numbered_files(path, "segment-")?;
        let mut tail = None;
        for &first in &segments {
            let file_path = segment_path(path, first);
            if first == 0 || first <= writer.closed.last().map_or(0, |&(_, last)| last) {
                return Err(invalid(format!("overlapping WAL segment at LSN {first}")));
            }
            if first > recovered.lsn.saturating_add(1) {
                return Err(gap(recovered.lsn + 1, first));
            }
            let is_tail = Some(&first) == segments.last();
            let bytes = fs::read(&file_path)?;
            let corrupt = |offset: usize| {
                invalid(format!(
                    "corrupt WAL batch in segment {first} at byte {offset}"
                ))
            };
            let mut last = first - 1;
            let mut torn = false;
            let mut offset = match decode_segment_header(&bytes) {
                Some((found, start)) if found == salt && start == first => SEGMENT_HEADER,
                Some(_) => {
                    return Err(invalid(format!(
                        "WAL segment {first} belongs to another log"
                    )));
                }
                // Only the final segment's first sync may be torn, and only if
                // no frame that verifies follows.
                None if is_tail && !has_valid_frame(&bytes, &salt) => {
                    torn = true;
                    bytes.len()
                }
                None => return Err(corrupt(0)),
            };
            let header = !torn;
            while offset < bytes.len() {
                let remaining = &bytes[offset..];
                let Some((size, records)) = decode_frame(remaining, &salt) else {
                    // A fully initialized segment may have a zero-filled suffix.
                    if bytes.len() as u64 == SEGMENT_SIZE && remaining.iter().all(|&byte| byte == 0)
                    {
                        break;
                    }
                    // Never trust a length from a frame that failed to verify:
                    // search every later byte for a frame that verifies.
                    if !is_tail || has_valid_frame(&remaining[1..], &salt) {
                        return Err(corrupt(offset));
                    }
                    torn = true;
                    break;
                };
                offset += size;
                for record in records {
                    let lsn = record.lsn();
                    if last.checked_add(1) != Some(lsn) {
                        return Err(invalid(format!(
                            "WAL LSN gap or overlap in segment {first} after {last}, found {lsn}"
                        )));
                    }
                    last = lsn;
                    if lsn <= checkpoint_lsn {
                        continue;
                    }
                    if recovered.lsn.checked_add(1) != Some(lsn) {
                        return Err(invalid(format!(
                            "WAL LSN gap or overlap after {}, found {lsn}",
                            recovered.lsn
                        )));
                    }
                    match record {
                        Record::Commit { writes, .. } => recovered.commits.push((lsn, writes)),
                        Record::Epoch {
                            descriptor, state, ..
                        } => {
                            recovered.descriptor = descriptor;
                            recovered.state = state;
                            recovered.commits.clear();
                        }
                    }
                    recovered.lsn = lsn;
                }
            }
            if is_tail {
                tail = Some((first, last, offset as u64, bytes.len() as u64, torn, header));
            } else if last < first {
                return Err(invalid(format!("empty non-final WAL segment {first}")));
            } else {
                writer.closed.push((first, last));
            }
        }
        if recovered.lsn < newest_checkpoint {
            return Err(invalid(format!(
                "corrupt WAL checkpoint {newest_checkpoint} and retained log ends at LSN {}",
                recovered.lsn
            )));
        }
        #[cfg(feature = "storage-fault-injection")]
        let expected_descriptor: &[u8] = &power_loss::bind(expected_descriptor)?;
        if recovered.descriptor != expected_descriptor {
            return Err(input_error("incompatible WAL environment descriptor"));
        }

        if let Some((first, _, _, _, _, false)) = tail {
            // A segment whose header never became durable holds nothing.
            fs::remove_file(segment_path(path, first))?;
        } else if let Some((first, last, bytes, mut capacity, torn, _)) = tail {
            let file = OpenOptions::new()
                .write(true)
                .open(segment_path(path, first))?;
            if torn {
                file.set_len(bytes)?;
                capacity = bytes;
            }
            // The preceding process may have died before syncing this segment.
            file.sync_data()?;
            if last == recovered.lsn {
                writer.active = Some(Segment {
                    first,
                    bytes,
                    capacity,
                    file,
                });
            } else if last >= first {
                writer.closed.push((first, last));
            } else {
                fs::remove_file(segment_path(path, first))?;
            }
        }
        directory.sync_all()?;
        writer.lsn = recovered.lsn;
        #[cfg(feature = "storage-fault-injection")]
        power_loss::start(path, salt)?;
        Ok((
            Self {
                path: path.to_owned(),
                directory,
                salt,
                _owner: owner,
                checkpoints: Mutex::new(Checkpoints {
                    latest: checkpoint_lsn,
                    oldest: checkpoints.first().copied().unwrap_or(checkpoint_lsn),
                }),
                writer: Mutex::new(writer),
            },
            recovered,
        ))
    }

    /// Append a consecutive batch as one checksummed frame with one data sync.
    pub fn append(&self, records: &[Record]) -> io::Result<()> {
        let mut writer = self.writer.lock().unwrap();
        if writer.failed {
            return Err(io::Error::other("WAL writer failed; reopen required"));
        }
        let Some(first) = records.first().map(Record::lsn) else {
            return Ok(());
        };
        let mut last = writer.lsn;
        for record in records {
            if last.checked_add(1) != Some(record.lsn()) {
                return Err(input_error(format!(
                    "WAL append needs consecutive LSNs after {last}, found {}",
                    record.lsn()
                )));
            }
            last = record.lsn();
        }
        let bytes = encode_frame(records, &self.salt)?;
        if let Err(error) = self.write_batch(&mut writer, first, last, &bytes) {
            writer.failed = true;
            return Err(error);
        }
        Ok(())
    }

    fn write_batch(
        &self,
        writer: &mut Writer,
        first: u64,
        last: u64,
        frame: &[u8],
    ) -> io::Result<()> {
        // Before any file is created, so a failure here leaves no new segment.
        fault_point("wal_before_write")?;
        let len = frame.len() as u64;
        if writer.active.as_ref().is_some_and(|segment| {
            segment.bytes > SEGMENT_HEADER as u64
                && segment.bytes.saturating_add(len) > SEGMENT_SIZE
        }) {
            let segment = writer.active.take().unwrap();
            writer.closed.push((segment.first, writer.lsn));
        }
        let created = writer.active.is_none();
        let mut data = Vec::new();
        if created {
            let file = new_file(&segment_path(&self.path, first))?;
            writer.active = Some(Segment {
                first,
                bytes: 0,
                capacity: 0,
                file,
            });
            // The header and the first frame share one write and one sync.
            data = encode_segment_header(&self.salt, first);
            data.extend_from_slice(frame);
        }
        let data = if created { &data[..] } else { frame };
        let segment = writer.active.as_mut().unwrap();
        let end = segment.bytes + data.len() as u64;
        if end <= SEGMENT_SIZE && segment.capacity < SEGMENT_SIZE {
            segment.reserve()?;
        }
        segment.file.write_all_at(data, segment.bytes)?;
        fault_point("wal_before_sync")?;
        segment.file.sync_data()?;
        #[cfg(feature = "storage-fault-injection")]
        power_loss::synced(&segment.file, Some((segment.bytes, data, frame)), "wal")?;
        if created {
            #[cfg(feature = "storage-fault-injection")]
            let _synced = power_loss::DirectorySync::begin(&self.path, "segment-name")?;
            // fdatasync covers the bytes. A new segment also needs its name synced.
            self.directory.sync_all()?;
        }
        segment.bytes = end;
        segment.capacity = segment.capacity.max(end);
        writer.lsn = last;
        Ok(())
    }

    /// Publish the snapshot of the state and descriptor at a durable LSN.
    /// An already superseded snapshot is ignored.
    pub fn checkpoint(&self, lsn: u64, descriptor: &[u8], state: &[u8]) -> io::Result<()> {
        let mut checkpoints = self.checkpoints.lock().unwrap();
        if lsn > self.writer.lock().unwrap().lsn {
            return Err(input_error("WAL checkpoint is ahead of the durable LSN"));
        }
        if lsn > checkpoints.latest {
            self.write_checkpoint(lsn, descriptor, state)?;
            // Keep the preceding checkpoint and the WAL needed to replay from it.
            checkpoints.oldest = checkpoints.latest;
            checkpoints.latest = lsn;
        }
        let covered = {
            let mut writer = self.writer.lock().unwrap();
            if writer.lsn <= checkpoints.latest
                && writer
                    .active
                    .as_ref()
                    .is_some_and(|segment| segment.bytes > SEGMENT_HEADER as u64)
            {
                let segment = writer.active.take().unwrap();
                let end = writer.lsn;
                writer.closed.push((segment.first, end));
            }
            writer
                .closed
                .iter()
                .take_while(|&&(_, last)| last <= checkpoints.oldest)
                .map(|&(first, _)| first)
                .collect::<Vec<_>>()
        };
        for first in &covered {
            remove_if_present(&segment_path(&self.path, *first))?;
        }
        for old in numbered_files(&self.path, "checkpoint-")? {
            if old < checkpoints.oldest {
                remove_if_present(&checkpoint_path(&self.path, old))?;
            }
        }
        #[cfg(feature = "storage-fault-injection")]
        let _synced = power_loss::DirectorySync::begin(&self.path, "reclaim")?;
        self.directory.sync_all()?;
        self.writer.lock().unwrap().closed.drain(..covered.len());
        Ok(())
    }

    fn write_checkpoint(&self, lsn: u64, descriptor: &[u8], state: &[u8]) -> io::Result<()> {
        #[cfg(feature = "storage-fault-injection")]
        let descriptor: &[u8] = &power_loss::bind(descriptor)?;
        let temporary = self.path.join(CHECKPOINT_TEMP);
        remove_if_present(&temporary)?;
        let mut file = new_file(&temporary)?;
        let mut checksum = crc32fast::Hasher::new();
        for bytes in [
            CHECKPOINT_MAGIC,
            &self.salt,
            &lsn.to_be_bytes(),
            &(descriptor.len() as u64).to_be_bytes(),
            descriptor,
            state,
        ] {
            file.write_all(bytes)?;
            checksum.update(bytes);
        }
        file.write_all(&checksum.finalize().to_be_bytes())?;
        file.sync_all()?;
        #[cfg(feature = "storage-fault-injection")]
        power_loss::synced(&file, None, "checkpoint")?;
        fs::rename(temporary, checkpoint_path(&self.path, lsn))?;
        #[cfg(feature = "storage-fault-injection")]
        let _synced = power_loss::DirectorySync::begin(&self.path, "checkpoint-name")?;
        self.directory.sync_all()
    }
}

impl Segment {
    fn reserve(&mut self) -> io::Result<()> {
        // Materialize the zeroes so later appends overwrite written blocks.
        // The batch's data sync also makes the newly reserved space durable.
        static ZEROES: [u8; 64 * 1024] = [0; 64 * 1024];
        while self.capacity < SEGMENT_SIZE {
            let len = (SEGMENT_SIZE - self.capacity).min(ZEROES.len() as u64) as usize;
            self.file.write_all_at(&ZEROES[..len], self.capacity)?;
            self.capacity += len as u64;
        }
        Ok(())
    }
}

fn open_directory(path: &Path) -> io::Result<File> {
    if !fs::symlink_metadata(path)?.is_dir() {
        return Err(input_error("WAL path must be a real directory"));
    }
    File::open(path)
}

fn new_file(path: &Path) -> io::Result<File> {
    OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(path)
}

fn require_file(path: &Path) -> io::Result<()> {
    if !fs::symlink_metadata(path)?.is_file() {
        return Err(invalid(format!("nonregular WAL file {}", path.display())));
    }
    Ok(())
}

fn numbered_files(path: &Path, prefix: &str) -> io::Result<Vec<u64>> {
    let mut files = Vec::new();
    for entry in fs::read_dir(path)? {
        let entry = entry?;
        let name = entry.file_name();
        if let Some(suffix) = name.as_encoded_bytes().strip_prefix(prefix.as_bytes()) {
            let lsn = std::str::from_utf8(suffix)
                .ok()
                .and_then(|suffix| suffix.parse::<u64>().ok())
                .filter(|lsn| lsn.to_string().as_bytes() == suffix)
                .ok_or_else(|| invalid(format!("invalid WAL filename {name:?}")))?;
            require_file(&entry.path())?;
            files.push(lsn);
        }
    }
    files.sort_unstable();
    Ok(files)
}

fn checkpoint_path(path: &Path, lsn: u64) -> PathBuf {
    path.join(format!("checkpoint-{lsn}"))
}

fn segment_path(path: &Path, first: u64) -> PathBuf {
    path.join(format!("segment-{first}"))
}

fn remove_if_present(path: &Path) -> io::Result<()> {
    match fs::remove_file(path) {
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
        result => result,
    }
}

fn gap(expected: u64, found: u64) -> io::Error {
    invalid(format!(
        "WAL LSN gap: expected {expected}, found segment {found}"
    ))
}

fn invalid(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message.into())
}

fn input_error(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidInput, message.into())
}

fn encode_segment_header(salt: &Salt, first: u64) -> Vec<u8> {
    let mut bytes = [SEGMENT_MAGIC, salt, &first.to_be_bytes()].concat();
    let crc = crc32fast::hash(&bytes);
    bytes.extend_from_slice(&crc.to_be_bytes());
    bytes
}

/// Salt and first LSN of a segment whose header verifies.
fn decode_segment_header(bytes: &[u8]) -> Option<(Salt, u64)> {
    let (header, crc) = bytes.get(..SEGMENT_HEADER)?.split_last_chunk::<4>()?;
    let mut rest = header.strip_prefix(SEGMENT_MAGIC)?;
    if crc32fast::hash(header) != u32::from_be_bytes(*crc) {
        return None;
    }
    let salt = *rest.split_first_chunk::<SALT>()?.0;
    rest = &rest[SALT..];
    Some((salt, read_u64(&mut rest)?))
}

fn frame_tag(salt: &Salt, len: u64, crc: u32) -> [u8; 8] {
    let digest = Sha256::new()
        .chain_update(FRAME_TAG)
        .chain_update(salt)
        .chain_update(len.to_be_bytes())
        .chain_update(crc.to_be_bytes())
        .finalize();
    *digest.first_chunk().unwrap()
}

fn encode_frame(records: &[Record], salt: &Salt) -> io::Result<Vec<u8>> {
    let capacity = FRAME_HEADER + records.iter().map(Record::encoded_len).sum::<usize>();
    let mut bytes = Vec::with_capacity(capacity);
    bytes.resize(FRAME_HEADER, 0);
    for record in records {
        bytes.extend_from_slice(&record.lsn().to_be_bytes());
        match record {
            Record::Commit { writes, .. } => {
                bytes.push(COMMIT);
                bytes.extend_from_slice(&(writes.len() as u64).to_be_bytes());
                for write in writes {
                    put_optional(&mut bytes, write.collection.as_deref().map(str::as_bytes));
                    put_blob(&mut bytes, write.key.as_bytes());
                    put_optional(&mut bytes, write.row.as_deref());
                }
            }
            Record::Epoch {
                descriptor, state, ..
            } => {
                bytes.push(EPOCH);
                #[cfg(feature = "storage-fault-injection")]
                let descriptor: &[u8] = &power_loss::bind(descriptor)?;
                put_blob(&mut bytes, descriptor);
                put_blob(&mut bytes, state);
            }
        }
    }
    let len = (bytes.len() - FRAME_HEADER) as u64;
    let crc = crc32fast::hash(&bytes[FRAME_HEADER..]);
    bytes[..8].copy_from_slice(&len.to_be_bytes());
    bytes[8..12].copy_from_slice(&crc.to_be_bytes());
    bytes[12..FRAME_HEADER].copy_from_slice(&frame_tag(salt, len, crc));
    Ok(bytes)
}

fn put_blob(bytes: &mut Vec<u8>, value: &[u8]) {
    bytes.extend_from_slice(&(value.len() as u64).to_be_bytes());
    bytes.extend_from_slice(value);
}

fn put_optional(bytes: &mut Vec<u8>, value: Option<&[u8]>) {
    if let Some(value) = value {
        bytes.push(1);
        put_blob(bytes, value);
    } else {
        bytes.push(0);
    }
}

/// A frame that verifies at the start of `bytes`: its size and records.
fn decode_frame(bytes: &[u8], salt: &Salt) -> Option<(usize, Vec<Record>)> {
    let (header, rest) = bytes.split_first_chunk::<FRAME_HEADER>()?;
    let len = u64::from_be_bytes(*header.first_chunk().unwrap());
    let crc = u32::from_be_bytes(header[8..12].try_into().unwrap());
    // Cheap bounds first; the salted tag before reading the body.
    if len < MIN_BODY as u64 || len > rest.len() as u64 || frame_tag(salt, len, crc) != header[12..]
    {
        return None;
    }
    let mut payload = &rest[..len as usize];
    if crc32fast::hash(payload) != crc {
        return None;
    }
    let mut records = Vec::new();
    while !payload.is_empty() {
        let lsn = read_u64(&mut payload)?;
        let kind = take(&mut payload, 1)?[0];
        records.push(decode_record(&mut payload, lsn, kind)?);
    }
    Some((FRAME_HEADER + len as usize, records))
}

fn decode_record(payload: &mut &[u8], lsn: u64, kind: u8) -> Option<Record> {
    Some(match kind {
        COMMIT => {
            let count = read_u64(payload)?;
            if count > (payload.len() / MIN_WRITE) as u64 {
                return None;
            }
            let mut writes = Vec::new();
            for _ in 0..count {
                let collection = read_optional(payload)?
                    .map(std::str::from_utf8)
                    .transpose()
                    .ok()?
                    .map(str::to_owned);
                let key = std::str::from_utf8(read_blob(payload)?).ok()?.to_owned();
                let row = read_optional(payload)?.map(<[u8]>::to_vec);
                writes.push(WriteEntry {
                    collection,
                    key,
                    row,
                });
            }
            Record::Commit { lsn, writes }
        }
        EPOCH => Record::Epoch {
            lsn,
            descriptor: read_blob(payload)?.to_vec(),
            state: read_blob(payload)?.to_vec(),
        },
        _ => return None,
    })
}

/// Whether a frame that verifies starts at any offset. Lengths read from
/// damaged frames are never used to skip ahead.
fn has_valid_frame(bytes: &[u8], salt: &Salt) -> bool {
    (0..bytes.len().saturating_sub(MIN_FRAME - 1))
        .any(|offset| decode_frame(&bytes[offset..], salt).is_some())
}

fn decode_checkpoint(bytes: &[u8], expected_lsn: u64) -> Option<(Salt, Recovered)> {
    let (body, crc) = bytes.split_last_chunk::<4>()?;
    let contents = body.strip_prefix(CHECKPOINT_MAGIC)?;
    let (salt, mut contents) = contents.split_first_chunk::<SALT>()?;
    let lsn = read_u64(&mut contents)?;
    if lsn != expected_lsn || u32::from_be_bytes(*crc) != crc32fast::hash(body) {
        return None;
    }
    let len = usize::try_from(read_u64(&mut contents)?).ok()?;
    let descriptor = take(&mut contents, len)?.to_vec();
    Some((
        *salt,
        Recovered {
            lsn,
            descriptor,
            state: contents.to_vec(),
            commits: Vec::new(),
        },
    ))
}

fn take<'a>(bytes: &mut &'a [u8], len: usize) -> Option<&'a [u8]> {
    let (value, rest) = bytes.split_at_checked(len)?;
    *bytes = rest;
    Some(value)
}

fn read_u64(bytes: &mut &[u8]) -> Option<u64> {
    let (value, rest) = bytes.split_first_chunk()?;
    *bytes = rest;
    Some(u64::from_be_bytes(*value))
}

fn read_blob<'a>(bytes: &mut &'a [u8]) -> Option<&'a [u8]> {
    let len = usize::try_from(read_u64(bytes)?).ok()?;
    take(bytes, len)
}

fn read_optional<'a>(bytes: &mut &'a [u8]) -> Option<Option<&'a [u8]>> {
    match take(bytes, 1)?[0] {
        0 => Some(None),
        1 => Some(Some(read_blob(bytes)?)),
        _ => None,
    }
}

#[cfg(feature = "storage-fault-injection")]
mod power_loss {
    //! Simulated power loss for tests/live/test_crash_power_loss.py. The
    //! tracker keeps what the last successful sync of each file and of the
    //! storage directory made durable. Each hook runs after its sync returns
    //! and before the caller relies on it, and first offers a cut: the chosen
    //! hook copies the directory with every unsynced 4 KiB block kept,
    //! reverted or torn and every unsynced name change applied or not, then
    //! exits. Other threads wait at their next hook until the process exits.
    use super::{
        Record, SEGMENT_HEADER, Salt, decode_frame, decode_segment_header, input_error, read_u64,
        take,
    };
    use serde_json::{Value, json};
    use std::collections::{BTreeMap, BTreeSet, HashMap};
    use std::fs::{self, File};
    use std::io;
    use std::os::fd::AsRawFd;
    use std::os::unix::fs::MetadataExt;
    use std::path::{Path, PathBuf};
    use std::sync::Mutex;
    use std::time::UNIX_EPOCH;

    const BLOCK: usize = 4096;
    const SECTOR: usize = 512;

    /// Inode and birth time, so a reused inode is a different file.
    type Id = (u64, u128);
    type Names = BTreeMap<String, Id>;

    struct Tracker {
        path: PathBuf,
        salt: Salt,
        kind: String,
        remaining: u64,
        output: PathBuf,
        seed: u64,
        trials: u64,
        names: Names,
        names_ticket: u64,
        tickets: u64,
        /// Durable length and contents; bytes past the vector are zeros.
        images: HashMap<Id, (usize, Vec<u8>)>,
        /// Synced WAL batches by first LSN, for the test oracle.
        batches: BTreeMap<u64, Value>,
    }

    static TRACKER: Mutex<Option<Tracker>> = Mutex::new(None);

    pub(super) fn start(path: &Path, salt: Salt) -> io::Result<()> {
        let Some(spec) = std::env::var_os("JAYDB_POWER_LOSS_CUT") else {
            return Ok(());
        };
        let (kind, remaining) = spec
            .to_str()
            .and_then(|spec| spec.split_once(':'))
            .and_then(|(kind, n)| Some((kind.to_owned(), n.parse().ok().filter(|&n| n > 0)?)))
            .ok_or_else(|| input_error("JAYDB_POWER_LOSS_CUT must be kind:occurrence"))?;
        let number = |name| {
            std::env::var(name).map_or(Ok(0), |value| {
                value
                    .parse()
                    .map_err(|_| input_error(format!("invalid {name}")))
            })
        };
        // Everything the host found or created is durable when it starts.
        let names = listing(path)?;
        let mut images = HashMap::new();
        for (name, id) in &names {
            images.insert(*id, trimmed(fs::read(path.join(name))?));
        }
        *TRACKER.lock().unwrap() = Some(Tracker {
            path: path.to_owned(),
            salt,
            kind,
            remaining,
            output: std::env::var_os("JAYDB_POWER_LOSS_DIR")
                .ok_or_else(|| input_error("JAYDB_POWER_LOSS_DIR is required"))?
                .into(),
            seed: number("JAYDB_POWER_LOSS_SEED")?,
            trials: number("JAYDB_POWER_LOSS_TRIALS")?.max(1),
            names,
            names_ticket: 0,
            tickets: 0,
            images,
            batches: BTreeMap::new(),
        });
        Ok(())
    }

    /// After a file sync. `write` is all data written since the previous
    /// sync and the WAL frame within it; without it the file is read back.
    pub(super) fn synced(
        file: &File,
        write: Option<(u64, &[u8], &[u8])>,
        kind: &str,
    ) -> io::Result<()> {
        let mut guard = TRACKER.lock().unwrap();
        let Some(tracker) = guard.as_mut() else {
            return Ok(());
        };
        let batch = write.map(|(_, _, frame)| summary(frame, &tracker.salt));
        // A WAL batch with an epoch record is offered as its own kind.
        let epoch = batch.as_ref().is_some_and(|batch| batch.2);
        tracker.offer(if epoch { "epoch" } else { kind })?;
        let metadata = file.metadata()?;
        let image = tracker.images.entry(id(&metadata)).or_default();
        if let (Some((offset, bytes, _)), Some((first, batch, _))) = (write, batch) {
            let end = offset as usize + bytes.len();
            image.1.resize(image.1.len().max(end), 0);
            image.1[offset as usize..end].copy_from_slice(bytes);
            image.0 = metadata.len() as usize;
            tracker.batches.insert(first, batch);
        } else {
            *image = trimmed(fs::read(format!("/proc/self/fd/{}", file.as_raw_fd()))?);
        }
        Ok(())
    }

    /// Lists the directory before its sync and records the listing as durable
    /// when dropped after the sync returns.
    pub(super) struct DirectorySync(Option<(Names, u64)>, &'static str);

    impl DirectorySync {
        pub(super) fn begin(path: &Path, kind: &'static str) -> io::Result<Self> {
            let mut guard = TRACKER.lock().unwrap();
            let Some(tracker) = guard.as_mut() else {
                return Ok(Self(None, kind));
            };
            tracker.tickets += 1;
            Ok(Self(Some((listing(path)?, tracker.tickets)), kind))
        }
    }

    impl Drop for DirectorySync {
        fn drop(&mut self) {
            let Some((names, ticket)) = self.0.take() else {
                return;
            };
            let mut guard = TRACKER.lock().unwrap();
            let tracker = guard.as_mut().unwrap();
            tracker.offer(self.1).expect("power-loss cut");
            // Concurrent syncs may finish out of order. The latest listing wins.
            if ticket > tracker.names_ticket {
                let current = listing(&tracker.path).expect("WAL directory listing");
                let live: BTreeSet<_> = names.values().chain(current.values()).collect();
                tracker.images.retain(|id, _| live.contains(id));
                tracker.names = names;
                tracker.names_ticket = ticket;
            }
        }
    }

    /// Rebinds a descriptor's controller entry to the normal executable, so
    /// the uninstrumented server can open the copies.
    pub(super) fn bind(descriptor: &[u8]) -> io::Result<Vec<u8>> {
        let Some(controller) = std::env::var_os("JAYDB_POWER_LOSS_CONTROLLER") else {
            return Ok(descriptor.to_vec());
        };
        fn blob<'a>(rest: &mut &'a [u8]) -> Option<&'a [u8]> {
            let len = usize::try_from(read_u64(rest)?).ok()?;
            take(rest, len)
        }
        let malformed = || input_error("descriptor has no server/controller entry");
        let mut rest = descriptor
            .strip_prefix(b"jaydb2-environment-v1\n")
            .ok_or_else(malformed)?;
        // Name and byte blobs, followed by the three u64 limits.
        while rest.len() > 24 {
            let name = blob(&mut rest).ok_or_else(malformed)?;
            let start = descriptor.len() - rest.len();
            blob(&mut rest).ok_or_else(malformed)?;
            if name == b"server/controller" {
                let controller = fs::read(controller)?;
                let mut bound = descriptor[..start].to_vec();
                bound.extend_from_slice(&(controller.len() as u64).to_be_bytes());
                bound.extend_from_slice(&controller);
                bound.extend_from_slice(rest);
                return Ok(bound);
            }
        }
        Err(malformed())
    }

    impl Tracker {
        fn offer(&mut self, kind: &str) -> io::Result<()> {
            if self.kind == kind || self.kind == "any" {
                self.remaining -= 1;
                if self.remaining == 0 {
                    self.cut()?;
                    std::process::exit(86);
                }
            }
            Ok(())
        }

        fn cut(&self) -> io::Result<()> {
            let mut now = Names::new();
            let mut contents = HashMap::new();
            for (name, id) in listing(&self.path)? {
                match fs::read(self.path.join(&name)) {
                    Ok(bytes) => {
                        now.insert(name, id);
                        contents.insert(id, bytes);
                    }
                    Err(error) if error.kind() == io::ErrorKind::NotFound => (),
                    Err(error) => return Err(error),
                }
            }
            // Unsynced frames exist only in the files.
            let mut batches = self.batches.clone();
            for id in now.iter().filter(|(name, _)| name.starts_with("segment-")) {
                let bytes = &contents[id.1][..];
                if decode_segment_header(bytes).is_none() {
                    continue;
                }
                let mut rest = &bytes[SEGMENT_HEADER..];
                while let Some((size, _)) = decode_frame(rest, &self.salt) {
                    let (first, batch, _) = summary(&rest[..size], &self.salt);
                    batches.insert(first, batch);
                    rest = &rest[size..];
                }
            }
            fs::create_dir(&self.output)?;
            let changed: BTreeSet<_> = (self.names.keys().chain(now.keys()))
                .filter(|&name| self.names.get(name) != now.get(name))
                .collect();
            for seed in (0..self.trials).map(|trial| self.seed.wrapping_add(trial)) {
                let mut random = Random(seed ^ 0x6a09e667f3bcc909);
                let directory = self.output.join(format!("trial-{seed}"));
                fs::create_dir(&directory)?;
                let mut names = self.names.clone();
                for &name in &changed {
                    if random.next() & 1 == 0 {
                        match now.get(name) {
                            Some(id) => names.insert(name.clone(), *id),
                            None => names.remove(name),
                        };
                    }
                }
                for (name, id) in &names {
                    let mut synced = Vec::new();
                    if let Some((len, bytes)) = self.images.get(id) {
                        synced.extend_from_slice(bytes);
                        synced.resize(*len, 0);
                    }
                    let len = synced.len();
                    let old = |index: usize| synced.get(index).copied().unwrap_or(0);
                    let Some(current) = contents.get(id) else {
                        fs::write(directory.join(name), &synced)?;
                        continue;
                    };
                    let (low, high) = (len.min(current.len()), len.max(current.len()));
                    let size = match random.below(3) {
                        _ if low == high => high,
                        0 => len,
                        1 => current.len(),
                        _ => low + random.below(high - low + 1),
                    };
                    let mut bytes = current.clone();
                    bytes.resize(size, 0);
                    for start in (0..size).step_by(BLOCK) {
                        let block = start..(start + BLOCK).min(size);
                        if block.clone().all(|index| old(index) == bytes[index]) {
                            continue;
                        }
                        // Keep, revert, or tear at sector granularity.
                        let choice = random.below(3);
                        for sector in block.clone().step_by(SECTOR) {
                            if choice == 1 || (choice == 2 && random.next() & 1 == 0) {
                                let end = (sector + SECTOR).min(block.end);
                                for (index, byte) in (sector..end).zip(&mut bytes[sector..end]) {
                                    *byte = old(index);
                                }
                            }
                        }
                    }
                    fs::write(directory.join(name), bytes)?;
                }
            }
            let manifest = json!({"kind": self.kind, "seed": self.seed, "trials": self.trials,
                                  "batches": batches.into_values().collect::<Vec<_>>()});
            fs::write(
                self.output.join("manifest.json"),
                serde_json::to_vec(&manifest)?,
            )
        }
    }

    fn id(metadata: &fs::Metadata) -> Id {
        let born = metadata
            .created()
            .ok()
            .and_then(|time| time.duration_since(UNIX_EPOCH).ok());
        (metadata.ino(), born.map_or(0, |born| born.as_nanos()))
    }

    fn listing(path: &Path) -> io::Result<Names> {
        let mut names = Names::new();
        for entry in fs::read_dir(path)? {
            let entry = entry?;
            match entry.metadata() {
                Ok(metadata) => {
                    names.insert(
                        entry.file_name().to_string_lossy().into_owned(),
                        id(&metadata),
                    );
                }
                Err(error) if error.kind() == io::ErrorKind::NotFound => (),
                Err(error) => return Err(error),
            }
        }
        Ok(names)
    }

    fn trimmed(mut bytes: Vec<u8>) -> (usize, Vec<u8>) {
        let len = bytes.len();
        bytes.truncate(
            bytes
                .iter()
                .rposition(|&byte| byte != 0)
                .map_or(0, |last| last + 1),
        );
        (len, bytes)
    }

    fn summary(frame: &[u8], salt: &Salt) -> (u64, Value, bool) {
        let (_, records) = decode_frame(frame, salt).expect("encoded WAL batch");
        let records: Vec<_> = records
            .into_iter()
            .map(|record| match record {
                Record::Commit { lsn, writes } => {
                    let keys: Vec<String> = writes
                        .iter()
                        .map(|write| write.key.chars().take(64).collect())
                        .collect();
                    json!({"lsn": lsn, "keys": keys})
                }
                Record::Epoch { lsn, .. } => json!({"lsn": lsn, "epoch": true}),
            })
            .collect();
        let epoch = records.iter().any(|record| record.get("epoch").is_some());
        (
            records[0]["lsn"].as_u64().unwrap(),
            Value::Array(records),
            epoch,
        )
    }

    /// SplitMix64, so each seed reproduces the same copy of the same cut.
    struct Random(u64);

    impl Random {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
            let mut value = self.0;
            value = (value ^ (value >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
            value = (value ^ (value >> 27)).wrapping_mul(0x94d049bb133111eb);
            value ^ (value >> 31)
        }

        fn below(&mut self, n: usize) -> usize {
            (self.next() % n as u64) as usize
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Temporary;
    use std::io::{BufRead, BufReader};
    use std::os::unix::process::ExitStatusExt;
    use std::process::{Command, Stdio};
    use std::sync::Barrier;

    const DESCRIPTOR: &[u8] = b"schema and limits";
    const INITIAL: &[u8] = b"initial state";
    const CHILD_PATH: &str = "JAYDB_TEST_WAL_CHILD_PATH";
    /// What a user who plants frame images in rows can produce: any salt
    /// but the log's own.
    const FOREIGN: Salt = [0x5a; SALT];

    fn database() -> (Temporary, PathBuf, Log) {
        let parent = Temporary::new(&std::env::temp_dir(), "jaydb-wal").unwrap();
        let path = parent.path.join("db");
        let log = Log::create(&path, DESCRIPTOR, INITIAL).unwrap();
        (parent, path, log)
    }

    fn writes(lsn: u64) -> Vec<WriteEntry> {
        vec![
            WriteEntry {
                collection: None,
                key: "user".into(),
                row: None,
            },
            WriteEntry {
                collection: Some("récords".into()),
                key: lsn.to_string(),
                row: Some(lsn.to_be_bytes().to_vec()),
            },
        ]
    }

    fn commit(lsn: u64) -> Record {
        Record::Commit {
            lsn,
            writes: writes(lsn),
        }
    }

    fn commits(range: std::ops::RangeInclusive<u64>) -> Vec<(u64, Vec<WriteEntry>)> {
        range.map(|lsn| (lsn, writes(lsn))).collect()
    }

    fn large_commit(lsn: u64, size: usize) -> Record {
        Record::Commit {
            lsn,
            writes: vec![WriteEntry {
                collection: Some("large".into()),
                key: lsn.to_string(),
                row: Some(vec![lsn as u8; size]),
            }],
        }
    }

    fn open_error(path: &Path, descriptor: &[u8]) -> io::Error {
        Log::open(path, descriptor).err().expect("open should fail")
    }

    fn active_bytes(log: &Log) -> usize {
        log.writer.lock().unwrap().active.as_ref().unwrap().bytes as usize
    }

    #[test]
    fn round_trip_and_consecutive_lsn() {
        let (_parent, path, log) = database();
        assert!(Log::create(&path, DESCRIPTOR, INITIAL).is_err());
        assert!(Log::open(&path, DESCRIPTOR).is_err());
        assert!(log.append(&[commit(1), commit(3)]).is_err());
        log.append(&[commit(1), commit(2)]).unwrap();
        assert!(log.append(&[commit(2)]).is_err());
        drop(log);

        let (log, recovered) = Log::open(&path, DESCRIPTOR).unwrap();
        assert_eq!(recovered.lsn, 2);
        assert_eq!(recovered.descriptor, DESCRIPTOR);
        assert_eq!(recovered.state, INITIAL);
        assert_eq!(recovered.commits, commits(1..=2));
        log.append(&[commit(3)]).unwrap();
        drop(log);
        assert_eq!(
            Log::open(&path, DESCRIPTOR).unwrap().1.commits,
            commits(1..=3)
        );
    }

    #[test]
    fn zero_filled_tail_recovers_at_the_logical_end() {
        let (_parent, path, log) = database();
        log.append(&[commit(1)]).unwrap();
        let segment = segment_path(&path, 1);
        let end = active_bytes(&log);
        let salt = log.salt;
        drop(log);
        let image = fs::read(&segment).unwrap();
        assert_eq!(image.len() as u64, SEGMENT_SIZE);
        assert!(image[end..].iter().all(|&byte| byte == 0));

        let (log, recovered) = Log::open(&path, DESCRIPTOR).unwrap();
        assert_eq!(recovered.commits, commits(1..=1));
        assert_eq!(active_bytes(&log), end);
        assert_eq!(fs::metadata(&segment).unwrap().len(), SEGMENT_SIZE);
        log.append(&[commit(2)]).unwrap();
        drop(log);
        assert_eq!(
            Log::open(&path, DESCRIPTOR).unwrap().1.commits,
            commits(1..=2)
        );
        assert_eq!(fs::metadata(&segment).unwrap().len(), SEGMENT_SIZE);

        let frame = encode_frame(&[commit(2)], &salt).unwrap();
        let mut torn = image;
        let partial = frame.len() - 1;
        torn[end..end + partial].copy_from_slice(&frame[..partial]);
        fs::write(&segment, &torn).unwrap();
        assert_eq!(
            Log::open(&path, DESCRIPTOR).unwrap().1.commits,
            commits(1..=1)
        );
        assert_eq!(fs::metadata(&segment).unwrap().len(), end as u64);

        // A zero header followed by a valid frame is corruption.
        fs::write(&segment, &torn[..end]).unwrap();
        let file = OpenOptions::new().write(true).open(&segment).unwrap();
        file.write_all_at(&frame, end as u64 + 7).unwrap();
        file.set_len(SEGMENT_SIZE).unwrap();
        let error = open_error(&path, DESCRIPTOR);
        assert!(error.to_string().contains("corrupt WAL batch"), "{error}");
    }

    #[test]
    fn every_torn_tail_byte_recovers_the_prefix() {
        let (_parent, path, log) = database();
        log.append(&[commit(1)]).unwrap();
        let segment = segment_path(&path, 1);
        let start = active_bytes(&log);
        // Canonical row bytes are opaque. A complete frame image in a
        // partially written row cannot verify without the log's salt.
        let mut nested = encode_frame(&[commit(3)], &FOREIGN).unwrap();
        nested.extend_from_slice(b"rest of row");
        log.append(&[Record::Commit {
            lsn: 2,
            writes: vec![WriteEntry {
                collection: None,
                key: "row".into(),
                row: Some(nested),
            }],
        }])
        .unwrap();
        let record_end = active_bytes(&log);
        drop(log);
        let image = fs::read(&segment).unwrap();
        for end in start..record_end {
            fs::write(&segment, &image[..end]).unwrap();
            let (log, recovered) = Log::open(&path, DESCRIPTOR).unwrap();
            assert_eq!(recovered.lsn, 1, "truncation at {end}");
            assert_eq!(recovered.commits, commits(1..=1));
            assert_eq!(fs::metadata(&segment).unwrap().len(), start as u64);
            log.append(&[commit(2)]).unwrap();
        }
        assert_eq!(
            Log::open(&path, DESCRIPTOR).unwrap().1.commits,
            commits(1..=2)
        );
    }

    #[test]
    fn torn_block_discards_the_whole_final_batch() {
        const BLOCK: usize = 4096;
        let (_parent, path, log) = database();
        log.append(&[commit(1), commit(2)]).unwrap();
        log.append(&[commit(3)]).unwrap();
        let start = active_bytes(&log);
        let segment = segment_path(&path, 1);
        log.append(&[large_commit(4, 3 * BLOCK), commit(5), commit(6)])
            .unwrap();
        drop(log);

        // Tear an aligned block in the first row while leaving the batch
        // header and the later records on disk intact.
        let torn = start.next_multiple_of(BLOCK) + BLOCK;
        OpenOptions::new()
            .write(true)
            .open(&segment)
            .unwrap()
            .write_all_at(&[0; BLOCK], torn as u64)
            .unwrap();

        let (_, recovered) = Log::open(&path, DESCRIPTOR).unwrap();
        assert_eq!(recovered.lsn, 3);
        assert_eq!(recovered.commits, commits(1..=3));
        assert_eq!(fs::metadata(&segment).unwrap().len(), start as u64);
    }

    #[test]
    fn interior_corruption_and_lsn_gaps_refuse_to_open() {
        let (_parent, path, log) = database();
        log.append(&[commit(1)]).unwrap();
        let segment = segment_path(&path, 1);
        let second = active_bytes(&log);
        log.append(&[commit(2), commit(3)]).unwrap();
        log.append(&[commit(4)]).unwrap();
        let salt = log.salt;
        drop(log);
        let image = fs::read(&segment).unwrap();
        for offset in [
            0,
            SEGMENT_MAGIC.len(),
            second,
            second + 7,
            second + 8,
            second + 12,
            second + FRAME_HEADER,
            second + FRAME_HEADER + RECORD_HEADER,
        ] {
            let mut corrupt = image.clone();
            corrupt[offset] ^= 0x80;
            fs::write(&segment, &corrupt).unwrap();
            let error = open_error(&path, DESCRIPTOR);
            assert!(error.to_string().contains("corrupt WAL batch"), "{error}");
            assert_eq!(fs::read(&segment).unwrap(), corrupt);
        }

        let mut gap = image[..second].to_vec();
        gap.extend_from_slice(&encode_frame(&[commit(3)], &salt).unwrap());
        fs::write(&segment, &gap).unwrap();
        let error = open_error(&path, DESCRIPTOR);
        assert!(error.to_string().contains("LSN gap"), "{error}");

        // The same corruption is recoverable at the very end.
        let mut torn = image[..second].to_vec();
        torn.extend_from_slice(&encode_frame(&[commit(2)], &salt).unwrap());
        *torn.last_mut().unwrap() ^= 1;
        fs::write(&segment, &torn).unwrap();
        assert_eq!(
            Log::open(&path, DESCRIPTOR).unwrap().1.commits,
            commits(1..=1)
        );
        assert_eq!(fs::metadata(&segment).unwrap().len(), second as u64);
    }

    #[test]
    fn frame_lengths_are_exact_and_salted() {
        let records = [
            commit(1),
            large_commit(2, 1000),
            Record::Commit {
                lsn: 3,
                writes: Vec::new(),
            },
        ];
        let salt = [7; SALT];
        let frame = encode_frame(&records, &salt).unwrap();
        assert_eq!(
            frame.len(),
            FRAME_HEADER + records.iter().map(Record::encoded_len).sum::<usize>()
        );
        assert_eq!(
            decode_frame(&frame, &salt).unwrap(),
            (frame.len(), records.into())
        );
        assert!(decode_frame(&frame, &FOREIGN).is_none());
        assert!(has_valid_frame(&[&[0; 3][..], &frame].concat(), &salt));
        assert!(!has_valid_frame(&[&[0; 3][..], &frame].concat(), &FOREIGN));
    }

    #[test]
    fn damaged_first_header_with_later_batches_refuses_to_open() {
        // Scenario A: media corruption overwrites the sector holding the first
        // batch's header with 0xff. Both lengths read u32::MAX in the former
        // format; recovery must not skip by them and truncate acknowledged data.
        const SECTOR: usize = 512;
        // Later batches must survive outside the damaged sector; if the
        // whole log fits in it, nothing distinguishes it from a lost first sync.
        for (spread, row) in [
            (SEGMENT_HEADER..SEGMENT_HEADER + FRAME_HEADER, 8),
            (0..SECTOR, 300),
            (0..SECTOR, 3000),
        ] {
            let (_parent, path, log) = database();
            for lsn in 1..=4 {
                log.append(&[large_commit(lsn, row)]).unwrap();
            }
            drop(log);
            let segment = segment_path(&path, 1);
            let mut image = fs::read(&segment).unwrap();
            image[spread.clone()].fill(0xff);
            fs::write(&segment, &image).unwrap();
            let error = open_error(&path, DESCRIPTOR);
            assert!(
                error.to_string().contains("corrupt WAL batch"),
                "{spread:?}: {error}"
            );
            assert_eq!(
                fs::read(&segment).unwrap(),
                image,
                "recovery changed the segment"
            );
        }

        // The same overwrite of the final, unacknowledged batch is a torn tail.
        let (_parent, path, log) = database();
        log.append(&[commit(1)]).unwrap();
        let start = active_bytes(&log);
        log.append(&[commit(2)]).unwrap();
        drop(log);
        let segment = segment_path(&path, 1);
        let mut image = fs::read(&segment).unwrap();
        image[start..start + FRAME_HEADER].fill(0xff);
        fs::write(&segment, &image).unwrap();
        assert_eq!(
            Log::open(&path, DESCRIPTOR).unwrap().1.commits,
            commits(1..=1)
        );
        assert_eq!(fs::metadata(&segment).unwrap().len(), start as u64);
    }

    #[test]
    fn planted_frame_images_in_a_torn_tail_do_not_block_recovery() {
        // Scenario B: the final, unacknowledged append loses its header sector
        // and keeps its payload, whose row holds frame images a user planted.
        const SECTOR: usize = 512;
        let (_parent, path, log) = database();
        log.append(&[commit(1), commit(2)]).unwrap();
        let start = active_bytes(&log);
        let mut row = vec![0x11; 700];
        for salt in [FOREIGN, [0; SALT], [0xff; SALT]] {
            for record in [commit(3), commit(4), large_commit(3, 100)] {
                row.extend_from_slice(&encode_frame(&[record], &salt).unwrap());
            }
        }
        row.extend_from_slice(&[0; 64]);
        log.append(&[Record::Commit {
            lsn: 3,
            writes: vec![WriteEntry {
                collection: Some("planted".into()),
                key: "row".into(),
                row: Some(row),
            }],
        }])
        .unwrap();
        let end = active_bytes(&log);
        drop(log);
        let segment = segment_path(&path, 1);
        let image = fs::read(&segment).unwrap();
        let sector_end = (start / SECTOR + 1) * SECTOR;
        assert!(
            sector_end < end,
            "the payload must extend past the header sector"
        );
        // Lost: the sector reverts to its earlier contents (zeros past the
        // acknowledged batches) or reads as 0xff.
        for fill in [0, 0xff] {
            let mut torn = image.clone();
            torn[start..sector_end].fill(fill);
            fs::write(&segment, &torn).unwrap();
            let (log, recovered) = Log::open(&path, DESCRIPTOR).unwrap();
            assert_eq!(recovered.commits, commits(1..=2), "fill {fill:#x}");
            assert_eq!(fs::metadata(&segment).unwrap().len(), start as u64);
            log.append(&[commit(3)]).unwrap();
            drop(log);
            assert_eq!(
                Log::open(&path, DESCRIPTOR).unwrap().1.commits,
                commits(1..=3)
            );
        }
    }

    #[test]
    fn segment_headers_bind_the_log_and_may_tear_only_without_frames() {
        let (_parent, path, log) = database();
        log.append(&[large_commit(1, SEGMENT_SIZE as usize)])
            .unwrap();
        log.append(&[commit(2)]).unwrap();
        assert_eq!(numbered_files(&path, "segment-").unwrap(), [1, 2]);
        drop(log);
        let tail = segment_path(&path, 2);
        let image = fs::read(&tail).unwrap();

        // The first sync of a new segment was lost: nothing in it verifies.
        for torn in [vec![0; image.len()], image[..SEGMENT_HEADER / 2].to_vec()] {
            fs::write(&tail, torn).unwrap();
            let (log, recovered) = Log::open(&path, DESCRIPTOR).unwrap();
            assert_eq!(recovered.lsn, 1);
            assert_eq!(numbered_files(&path, "segment-").unwrap(), [1]);
            log.append(&[commit(2)]).unwrap();
            drop(log);
            assert_eq!(Log::open(&path, DESCRIPTOR).unwrap().1.lsn, 2);
        }

        // A damaged header before a frame that verifies is corruption, and a
        // segment from another log is refused.
        let image = fs::read(&tail).unwrap();
        let mut damaged = image.clone();
        damaged[3] ^= 1;
        fs::write(&tail, &damaged).unwrap();
        let error = open_error(&path, DESCRIPTOR);
        assert!(error.to_string().contains("corrupt WAL batch"), "{error}");
        let mut foreign = encode_segment_header(&FOREIGN, 2);
        foreign.extend_from_slice(&image[SEGMENT_HEADER..]);
        fs::write(&tail, &foreign).unwrap();
        let error = open_error(&path, DESCRIPTOR);
        assert!(error.to_string().contains("another log"), "{error}");
        fs::write(&tail, &image).unwrap();

        // The head segment's header cannot tear: a later segment exists.
        let head = segment_path(&path, 1);
        let mut head_image = fs::read(&head).unwrap();
        head_image[..SEGMENT_HEADER].fill(0);
        fs::write(&head, &head_image).unwrap();
        let error = open_error(&path, DESCRIPTOR);
        assert!(error.to_string().contains("corrupt WAL batch"), "{error}");
    }

    #[test]
    fn checkpoint_replays_only_later_commits() {
        let (_parent, path, log) = database();
        log.append(&[commit(1), commit(2)]).unwrap();
        log.checkpoint(1, DESCRIPTOR, b"after one").unwrap();
        log.append(&[commit(3)]).unwrap();
        assert!(log.checkpoint(4, DESCRIPTOR, b"future").is_err());
        drop(log);

        let (_, recovered) = Log::open(&path, DESCRIPTOR).unwrap();
        assert_eq!(recovered.lsn, 3);
        assert_eq!(recovered.state, b"after one");
        assert_eq!(recovered.commits, commits(2..=3));
    }

    #[test]
    fn checkpoint_and_appends_can_run_concurrently() {
        let (_parent, path, log) = database();
        let state = vec![0xa5; 2 * SEGMENT_SIZE as usize];
        log.append(&[commit(1)]).unwrap();
        let start = Barrier::new(2);
        std::thread::scope(|scope| {
            scope.spawn(|| {
                start.wait();
                log.checkpoint(1, DESCRIPTOR, &state).unwrap();
            });
            start.wait();
            for lsn in 2..=40 {
                log.append(&[commit(lsn)]).unwrap();
            }
        });
        drop(log);

        let (_, recovered) = Log::open(&path, DESCRIPTOR).unwrap();
        assert_eq!(recovered.lsn, 40);
        assert_eq!(recovered.state, state);
        assert_eq!(recovered.commits, commits(2..=40));
    }

    #[test]
    fn rotates_and_reclaims_only_covered_segments() {
        let (_parent, path, log) = database();
        let size = SEGMENT_SIZE as usize / 2;
        log.append(&[large_commit(1, size), large_commit(2, size)])
            .unwrap();
        log.append(&[large_commit(3, size)]).unwrap();
        log.append(&[large_commit(4, size)]).unwrap();
        assert_eq!(numbered_files(&path, "segment-").unwrap(), [1, 3, 4]);
        log.checkpoint(1, DESCRIPTOR, b"first").unwrap();
        assert_eq!(numbered_files(&path, "segment-").unwrap(), [1, 3, 4]);
        log.checkpoint(2, DESCRIPTOR, b"second").unwrap();
        assert_eq!(numbered_files(&path, "segment-").unwrap(), [1, 3, 4]);
        assert_eq!(numbered_files(&path, "checkpoint-").unwrap(), [1, 2]);
        drop(log);

        let (log, recovered) = Log::open(&path, DESCRIPTOR).unwrap();
        assert_eq!(recovered.lsn, 4);
        assert_eq!(recovered.state, b"second");
        assert_eq!(
            recovered.commits.iter().map(|c| c.0).collect::<Vec<_>>(),
            [3, 4]
        );
        log.checkpoint(4, DESCRIPTOR, b"fourth").unwrap();
        assert_eq!(numbered_files(&path, "segment-").unwrap(), [3, 4]);
        assert_eq!(numbered_files(&path, "checkpoint-").unwrap(), [2, 4]);
        log.append(&[commit(5)]).unwrap();
        drop(log);
        assert_eq!(
            Log::open(&path, DESCRIPTOR).unwrap().1.commits,
            commits(5..=5)
        );
    }

    #[test]
    fn checkpoint_fallback_replays_retained_segments() {
        let (_parent, path, log) = database();
        log.append(&[commit(1)]).unwrap();
        log.checkpoint(1, DESCRIPTOR, b"one").unwrap();
        log.append(&[commit(2)]).unwrap();
        // Retrying cleanup must keep the previous checkpoint.
        log.checkpoint(1, DESCRIPTOR, b"one").unwrap();
        drop(log);
        let newest = checkpoint_path(&path, 1);
        let valid = fs::read(&newest).unwrap();
        fs::write(&newest, b"corrupt").unwrap();
        let (log, recovered) = Log::open(&path, DESCRIPTOR).unwrap();
        assert_eq!(recovered.state, INITIAL);
        assert_eq!(recovered.commits, commits(1..=2));

        drop(log);
        fs::write(&newest, valid).unwrap();
        let (log, _) = Log::open(&path, DESCRIPTOR).unwrap();
        log.checkpoint(2, DESCRIPTOR, b"two").unwrap();
        assert_eq!(numbered_files(&path, "segment-").unwrap(), [2]);
        drop(log);
        let checkpoint_two = checkpoint_path(&path, 2);
        let mut corrupt = fs::read(&checkpoint_two).unwrap();
        *corrupt.last_mut().unwrap() ^= 1;
        fs::write(checkpoint_two, corrupt).unwrap();
        let (log, recovered) = Log::open(&path, DESCRIPTOR).unwrap();
        assert_eq!(recovered.lsn, 2);
        assert_eq!(recovered.state, b"one");
        assert_eq!(recovered.commits, commits(2..=2));

        drop(log);
        fs::remove_file(segment_path(&path, 2)).unwrap();
        let error = open_error(&path, DESCRIPTOR);
        assert!(error.to_string().contains("retained log ends"), "{error}");
        fs::remove_file(&newest).unwrap();
        let error = open_error(&path, DESCRIPTOR);
        assert!(error.to_string().contains("no valid checkpoint"), "{error}");
    }

    #[test]
    fn epoch_replaces_state_descriptor_and_replay_base() {
        let (_parent, path, log) = database();
        log.append(&[
            commit(1),
            Record::Epoch {
                lsn: 2,
                descriptor: b"new schema".to_vec(),
                state: b"migrated".to_vec(),
            },
            commit(3),
        ])
        .unwrap();
        drop(log);

        let error = open_error(&path, DESCRIPTOR);
        assert!(
            error.to_string().contains("environment descriptor"),
            "{error}"
        );
        let (log, recovered) = Log::open(&path, b"new schema").unwrap();
        assert_eq!(recovered.lsn, 3);
        assert_eq!(recovered.descriptor, b"new schema");
        assert_eq!(recovered.state, b"migrated");
        assert_eq!(recovered.commits, commits(3..=3));
        log.checkpoint(3, b"new schema", b"after migration and commit")
            .unwrap();
        drop(log);
        let (_, recovered) = Log::open(&path, b"new schema").unwrap();
        assert_eq!(recovered.lsn, 3);
        assert_eq!(recovered.state, b"after migration and commit");
        assert!(recovered.commits.is_empty());
    }

    #[test]
    #[cfg(feature = "storage-fault-injection")]
    fn wal_fsync_failure_is_fail_stop() {
        if let Some(path) = std::env::var_os(CHILD_PATH) {
            let (log, _) = Log::open(Path::new(&path), DESCRIPTOR).unwrap();
            assert_eq!(
                log.append(&[commit(1)]).unwrap_err().raw_os_error(),
                Some(libc::EIO)
            );
            let error = log.append(&[commit(1)]).unwrap_err();
            assert!(error.to_string().contains("writer failed"), "{error}");
            assert!(log.append(&[commit(2)]).is_err());
            let image = fs::read(segment_path(Path::new(&path), 1)).unwrap();
            assert_eq!(decode_segment_header(&image), Some((log.salt, 1)));
            let (end, records) = decode_frame(&image[SEGMENT_HEADER..], &log.salt).unwrap();
            assert_eq!(records, [commit(1)]);
            assert!(image[SEGMENT_HEADER + end..].iter().all(|&byte| byte == 0));
            return;
        }

        let (_parent, path, log) = database();
        drop(log);
        let output = Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "wal::tests::wal_fsync_failure_is_fail_stop"])
            .env(CHILD_PATH, path)
            .env("JAYDB_STORAGE_FAULT", "wal_before_sync")
            .env_remove("JAYDB_STORAGE_BARRIER")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
        assert!(String::from_utf8_lossy(&output.stdout).contains("1 passed"));
    }

    #[test]
    fn wal_sigkill_keeps_every_reported_batch() {
        use std::hash::{BuildHasher, Hasher, RandomState};

        if let Some(path) = std::env::var_os(CHILD_PATH) {
            let (log, _) = Log::open(Path::new(&path), DESCRIPTOR).unwrap();
            for first in (1..).step_by(3) {
                let last = first + 2;
                let batch = (first..=last)
                    .map(|lsn| large_commit(lsn, 32 * 1024))
                    .collect::<Vec<_>>();
                log.append(&batch).unwrap();
                println!("wal-durable {last}");
            }
            unreachable!();
        }

        let (_parent, path, log) = database();
        drop(log);
        let mut child = Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "wal::tests::wal_sigkill_keeps_every_reported_batch",
                "--nocapture",
            ])
            .env(CHILD_PATH, &path)
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();
        let mut stdout = BufReader::new(child.stdout.take().unwrap());
        let mut line = String::new();
        let mut reported = Vec::new();
        let acknowledge = |line: &str, reported: &mut Vec<u64>| {
            if let Some((_, lsn)) = line
                .strip_suffix('\n')
                .and_then(|s| s.split_once("wal-durable "))
            {
                reported.push(lsn.parse().unwrap());
            }
        };
        while reported.is_empty() && stdout.read_line(&mut line).unwrap() != 0 {
            acknowledge(&line, &mut reported);
            line.clear();
        }
        assert_eq!(reported, [3], "child failed to acknowledge the first batch");
        let random = RandomState::new().build_hasher().finish();
        std::thread::sleep(std::time::Duration::from_millis(1 + random % 15));
        child.kill().unwrap();
        assert_eq!(child.wait().unwrap().signal(), Some(libc::SIGKILL));
        while stdout.read_line(&mut line).unwrap() != 0 {
            acknowledge(&line, &mut reported);
            line.clear();
        }
        assert!(
            reported
                .iter()
                .copied()
                .eq((3..).step_by(3).take(reported.len()))
        );

        let (_, recovered) = Log::open(&path, DESCRIPTOR).unwrap();
        assert!(recovered.lsn >= *reported.last().unwrap());
        assert_eq!(recovered.lsn % 3, 0);
        assert_eq!(recovered.commits.len() as u64, recovered.lsn);
        for (lsn, entries) in recovered.commits {
            assert_eq!(
                Record::Commit {
                    lsn,
                    writes: entries
                },
                large_commit(lsn, 32 * 1024)
            );
        }
    }
}
