//! Live engine write-ahead log, checkpoints and recovery. See docs/live-engine.md.
#![allow(dead_code)]

use crate::storage::fault_point;
use std::fs::{self, DirBuilder, File, OpenOptions};
use std::io::{self, Write};
use std::os::unix::fs::{DirBuilderExt, FileExt, OpenOptionsExt};
use std::path::{Path, PathBuf};
use std::sync::Mutex;

const SEGMENT_SIZE: u64 = 8 * 1024 * 1024;
const CHECKPOINT_MAGIC: &[u8] = b"jaydb2-wal-checkpoint-v1\n";
const CHECKPOINT_TEMP: &str = ".checkpoint.tmp";
const OWNER: &str = "owner.lock";
const FRAME_HEADER: usize = 8;
const RECORD_HEADER: usize = 8 + 1; // LSN, kind
const REPEATED_LENGTH: usize = FRAME_HEADER + RECORD_HEADER;
const MIN_FRAME: usize = REPEATED_LENGTH + 4 + 4;
const COMMIT: u8 = 1;
const EPOCH: u8 = 2;

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
        let log = Self {
            path: path.to_owned(),
            directory,
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
        let mut recovered = loop {
            let lsn = checkpoints
                .pop()
                .ok_or_else(|| invalid("WAL has no valid checkpoint"))?;
            let bytes = fs::read(checkpoint_path(path, lsn))?;
            if let Some(recovered) = decode_checkpoint(&bytes, lsn) {
                break recovered;
            }
        };
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
            let mut offset = 0;
            let mut last = first - 1;
            let mut torn = false;
            while offset < bytes.len() {
                let remaining = &bytes[offset..];
                let Some((size, records)) = decode_batch(remaining) else {
                    // A fully initialized segment may have a zero-filled suffix.
                    if bytes.len() as u64 == SEGMENT_SIZE && remaining.iter().all(|&byte| byte == 0)
                    {
                        break;
                    }
                    if !is_tail || has_later_batch(remaining) {
                        return Err(invalid(format!(
                            "corrupt WAL batch in segment {first} at byte {offset}"
                        )));
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
                tail = Some((first, last, offset as u64, bytes.len() as u64, torn));
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
        if recovered.descriptor != expected_descriptor {
            return Err(input_error("incompatible WAL environment descriptor"));
        }

        if let Some((first, last, bytes, mut capacity, torn)) = tail {
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
        Ok((
            Self {
                path: path.to_owned(),
                directory,
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
        let bytes = encode_batch(records)?;
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
        bytes: &[u8],
    ) -> io::Result<()> {
        let len = bytes.len() as u64;
        if writer.active.as_ref().is_some_and(|segment| {
            segment.bytes != 0 && segment.bytes.saturating_add(len) > SEGMENT_SIZE
        }) {
            let segment = writer.active.take().unwrap();
            writer.closed.push((segment.first, writer.lsn));
        }
        let created = writer.active.is_none();
        if created {
            let file = new_file(&segment_path(&self.path, first))?;
            writer.active = Some(Segment {
                first,
                bytes: 0,
                capacity: 0,
                file,
            });
        }
        let segment = writer.active.as_mut().unwrap();
        fault_point("wal_before_write")?;
        let end = segment.bytes + len;
        if end <= SEGMENT_SIZE && segment.capacity < SEGMENT_SIZE {
            segment.reserve()?;
        }
        segment.file.write_all_at(bytes, segment.bytes)?;
        fault_point("wal_before_sync")?;
        segment.file.sync_data()?;
        if created {
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
                    .is_some_and(|segment| segment.bytes != 0)
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
        self.directory.sync_all()?;
        self.writer.lock().unwrap().closed.drain(..covered.len());
        Ok(())
    }

    fn write_checkpoint(&self, lsn: u64, descriptor: &[u8], state: &[u8]) -> io::Result<()> {
        let temporary = self.path.join(CHECKPOINT_TEMP);
        remove_if_present(&temporary)?;
        let mut file = new_file(&temporary)?;
        let mut checksum = crc32fast::Hasher::new();
        for bytes in [
            CHECKPOINT_MAGIC,
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
        fs::rename(temporary, checkpoint_path(&self.path, lsn))?;
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

fn encode_batch(records: &[Record]) -> io::Result<Vec<u8>> {
    let mut bytes = vec![0; FRAME_HEADER];
    for (index, record) in records.iter().enumerate() {
        bytes.extend_from_slice(&record.lsn().to_be_bytes());
        bytes.push(match record {
            Record::Commit { .. } => COMMIT,
            Record::Epoch { .. } => EPOCH,
        });
        if index == 0 {
            bytes.extend_from_slice(&[0; 4]);
        }
        match record {
            Record::Commit { writes, .. } => {
                bytes.extend_from_slice(&length(writes.len())?.to_be_bytes());
                for write in writes {
                    put_optional(&mut bytes, write.collection.as_deref().map(str::as_bytes))?;
                    put_blob(&mut bytes, write.key.as_bytes())?;
                    put_optional(&mut bytes, write.row.as_deref())?;
                }
            }
            Record::Epoch {
                descriptor, state, ..
            } => {
                put_blob(&mut bytes, descriptor)?;
                put_blob(&mut bytes, state)?;
            }
        }
    }
    let size = length(bytes.len() - FRAME_HEADER)?.to_be_bytes();
    bytes[REPEATED_LENGTH..REPEATED_LENGTH + 4].copy_from_slice(&size);
    let crc = crc32fast::hash(&bytes[FRAME_HEADER..]);
    bytes[..4].copy_from_slice(&size);
    bytes[4..FRAME_HEADER].copy_from_slice(&crc.to_be_bytes());
    Ok(bytes)
}

fn length(len: usize) -> io::Result<u32> {
    u32::try_from(len).map_err(|_| input_error("WAL data exceeds the format size limit"))
}

fn put_blob(bytes: &mut Vec<u8>, value: &[u8]) -> io::Result<()> {
    bytes.extend_from_slice(&length(value.len())?.to_be_bytes());
    bytes.extend_from_slice(value);
    Ok(())
}

fn put_optional(bytes: &mut Vec<u8>, value: Option<&[u8]>) -> io::Result<()> {
    if let Some(value) = value {
        bytes.push(1);
        put_blob(bytes, value)?;
    } else {
        bytes.push(0);
    }
    Ok(())
}

fn decode_batch(mut bytes: &[u8]) -> Option<(usize, Vec<Record>)> {
    let len = read_u32(&mut bytes)? as usize;
    let crc = read_u32(&mut bytes)?;
    let mut payload = take(&mut bytes, len)?;
    let contents = payload;
    let lsn = read_u64(&mut payload)?;
    let kind = take(&mut payload, 1)?[0];
    if read_u32(&mut payload)? as usize != len || crc32fast::hash(contents) != crc {
        return None;
    }
    let mut records = vec![decode_record(&mut payload, lsn, kind)?];
    while !payload.is_empty() {
        let lsn = read_u64(&mut payload)?;
        let kind = take(&mut payload, 1)?[0];
        records.push(decode_record(&mut payload, lsn, kind)?);
    }
    Some((FRAME_HEADER + len, records))
}

fn decode_record(payload: &mut &[u8], lsn: u64, kind: u8) -> Option<Record> {
    Some(match kind {
        COMMIT => {
            let count = read_u32(payload)? as usize;
            if count > payload.len() / 6 {
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

fn has_later_batch(bytes: &[u8]) -> bool {
    // When both lengths agree, skip the damaged batch so a frame encoded
    // inside an opaque row cannot masquerade as later WAL data.
    let first_length = bytes.first_chunk::<4>().copied().map(u32::from_be_bytes);
    let repeated_length = bytes
        .get(REPEATED_LENGTH..)
        .and_then(<[u8]>::first_chunk::<4>)
        .copied()
        .map(u32::from_be_bytes);
    let start = match (first_length, repeated_length) {
        (Some(length), Some(repeated))
            if length == repeated && length as usize >= MIN_FRAME - FRAME_HEADER =>
        {
            FRAME_HEADER.saturating_add(length as usize)
        }
        _ => 1,
    };
    (start..bytes.len().saturating_sub(MIN_FRAME - 1))
        .any(|offset| decode_batch(&bytes[offset..]).is_some())
}

fn decode_checkpoint(bytes: &[u8], expected_lsn: u64) -> Option<Recovered> {
    let (body, crc) = bytes.split_last_chunk::<4>()?;
    let mut contents = body.strip_prefix(CHECKPOINT_MAGIC)?;
    let lsn = read_u64(&mut contents)?;
    if lsn != expected_lsn || u32::from_be_bytes(*crc) != crc32fast::hash(body) {
        return None;
    }
    let len = usize::try_from(read_u64(&mut contents)?).ok()?;
    let descriptor = take(&mut contents, len)?.to_vec();
    Some(Recovered {
        lsn,
        descriptor,
        state: contents.to_vec(),
        commits: Vec::new(),
    })
}

fn take<'a>(bytes: &mut &'a [u8], len: usize) -> Option<&'a [u8]> {
    let (value, rest) = bytes.split_at_checked(len)?;
    *bytes = rest;
    Some(value)
}

fn read_u32(bytes: &mut &[u8]) -> Option<u32> {
    let (value, rest) = bytes.split_first_chunk()?;
    *bytes = rest;
    Some(u32::from_be_bytes(*value))
}

fn read_u64(bytes: &mut &[u8]) -> Option<u64> {
    let (value, rest) = bytes.split_first_chunk()?;
    *bytes = rest;
    Some(u64::from_be_bytes(*value))
}

fn read_blob<'a>(bytes: &mut &'a [u8]) -> Option<&'a [u8]> {
    let len = read_u32(bytes)? as usize;
    take(bytes, len)
}

fn read_optional<'a>(bytes: &mut &'a [u8]) -> Option<Option<&'a [u8]>> {
    match take(bytes, 1)?[0] {
        0 => Some(None),
        1 => Some(Some(read_blob(bytes)?)),
        _ => None,
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

        let frame = encode_batch(&[commit(2)]).unwrap();
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
        // Canonical row bytes are opaque. Even a complete encoded frame in a
        // partially written row must not count as a later batch.
        let mut nested = encode_batch(&[commit(3)]).unwrap();
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
        drop(log);
        let image = fs::read(&segment).unwrap();
        for offset in [
            second,
            second + 4,
            second + FRAME_HEADER,
            second + REPEATED_LENGTH,
        ] {
            let mut corrupt = image.clone();
            corrupt[offset] ^= 0x80;
            fs::write(&segment, &corrupt).unwrap();
            let error = open_error(&path, DESCRIPTOR);
            assert!(error.to_string().contains("corrupt WAL batch"), "{error}");
            assert_eq!(fs::read(&segment).unwrap(), corrupt);
        }

        let mut gap = image[..second].to_vec();
        gap.extend_from_slice(&encode_batch(&[commit(3)]).unwrap());
        fs::write(&segment, &gap).unwrap();
        let error = open_error(&path, DESCRIPTOR);
        assert!(error.to_string().contains("LSN gap"), "{error}");

        // The same corruption is recoverable at the very end.
        let mut torn = image[..second].to_vec();
        torn.extend_from_slice(&encode_batch(&[commit(2)]).unwrap());
        *torn.last_mut().unwrap() ^= 1;
        fs::write(&segment, &torn).unwrap();
        assert_eq!(
            Log::open(&path, DESCRIPTOR).unwrap().1.commits,
            commits(1..=1)
        );
        assert_eq!(fs::metadata(&segment).unwrap().len(), second as u64);
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
            let (end, records) = decode_batch(&image).unwrap();
            assert_eq!(records, [commit(1)]);
            assert!(image[end..].iter().all(|&byte| byte == 0));
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
