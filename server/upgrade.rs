//! Offline import of the complete-image format used before the live engine.
use super::{Log, storage_error};
use crate::{Error, Limits, Options, Program, Result, Snapshot, Temporary};
use crate::{capture, export_schema, json_helper, programs, text};
use sha2::{Digest, Sha256};
use std::fs::{self, DirBuilder, File, OpenOptions};
use std::io::{self, Read, Seek, SeekFrom};
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt};
use std::path::{Path, PathBuf};
use std::process::Command;

const IMAGE: &str = "snapshot";
const ENVIRONMENT: &str = "environment";
const OWNER: &str = "owner.lock";
const MAGIC: &[u8] = b"jaydb2-image-v1\n";
const OVERHEAD: usize = MAGIC.len() + 64 + 4 * 8 + 32;
const LEGACY_PATHS: &str = "Keep the old checkout and binary at their original paths and run the upgrader from a second checkout.";

pub(crate) struct Source {
    pub directory: PathBuf,
    pub executable: PathBuf,
}

pub(crate) fn run(options: &Options, destination: &Path, source: &Source) -> Result<()> {
    if !fs::symlink_metadata(&source.directory)
        .map_err(storage_error)?
        .is_dir()
    {
        return Err(failure("legacy storage must be a real directory"));
    }
    let old = fs::canonicalize(&source.directory).map_err(storage_error)?;
    let executable = fs::canonicalize(&source.executable).map_err(storage_error)?;
    let parent = fs::canonicalize(
        destination
            .parent()
            .filter(|parent| !parent.as_os_str().is_empty())
            .unwrap_or(Path::new(".")),
    )
    .map_err(storage_error)?;
    let temp = fs::canonicalize(std::env::temp_dir()).map_err(storage_error)?;
    if parent.starts_with(&old) || temp.starts_with(&old) {
        return Err(failure("upgrade paths must be outside legacy storage"));
    }
    match fs::symlink_metadata(destination) {
        Err(error) if error.kind() == io::ErrorKind::NotFound => (),
        Err(error) => return Err(storage_error(error)),
        Ok(_) => return Err(failure("upgrade destination must be a new directory")),
    }
    let destination = parent.join(
        destination
            .file_name()
            .ok_or_else(|| failure("missing upgrade destination directory name"))?,
    );

    let owner = regular_file(&old.join(OWNER)).map_err(storage_error)?;
    // Same exclusive lock as legacy open. All original files are opened read-only.
    owner.try_lock().map_err(|error| {
        failure(format!(
            "cannot lock legacy storage for offline upgrade: {error}"
        ))
    })?;
    let image = regular_file(&old.join(IMAGE)).map_err(storage_error)?;
    let mut environment = regular_file(&old.join(ENVIRONMENT)).map_err(storage_error)?;
    check_controller(&mut environment, &executable)?;

    let frozen = Temporary::new(&temp, "jaydb-upgrade-config")?;
    let report = json_helper(
        &options.root.join("tools/service/stage.mjs"),
        &[
            "recover".into(),
            frozen.path.clone().into_os_string(),
            options.configuration.clone().into_os_string(),
            options.source.clone().into_os_string(),
            options.kernel.clone().into_os_string(),
        ],
    )?;
    let limits = Limits::read(&report)?;
    let recover = Program::load(text(programs(&report)?, "recover")?.into(), 0)?;
    if recover.run(&[], options.threads)? != [1] {
        return Err(Error::new("CONFIGURATION", "invalid configuration"));
    }
    let schema = export_schema(&report, &limits, options.threads)?;

    let replica = Temporary::new(&temp, "jaydb-upgrade-image")?;
    let snapshot = replica.path.join(IMAGE);
    let maximum = limits.state.saturating_add(OVERHEAD as u64);
    if image.metadata().map_err(storage_error)?.len() > maximum
        || copy_file(image.take(maximum.saturating_add(1)), &snapshot).map_err(storage_error)?
            > maximum
    {
        return Err(failure("oversized authoritative snapshot"));
    }
    let bytes = fs::read(snapshot).map_err(storage_error)?;
    let state = decode_image(&bytes, &limits)?;
    if Snapshot::load(schema, 0, state)
        .map_err(super::state_error)?
        .save()
        != state
    {
        return Err(failure("legacy state is not in canonical store order"));
    }
    File::create_new(replica.path.join(OWNER)).map_err(storage_error)?;
    copy_file(environment, &replica.path.join(ENVIRONMENT)).map_err(storage_error)?;

    // Verify using the original controller, which includes its own executable
    // bytes in the exact descriptor. Feed it the same frozen administrator
    // sources used for the destination to avoid a second read of mutable inputs.
    let output = capture(
        Command::new(executable)
            .arg("--configuration")
            .arg(frozen.path.join("public/Configuration.bend"))
            .arg("--storage")
            .arg(&replica.path)
            .args(["--storage-mode", "open", "--threads"])
            .arg(options.threads.to_string())
            .arg("--bend-source")
            .arg(&options.source)
            .arg("--bendtt")
            .arg(&options.kernel)
            .env("TMPDIR", &temp),
        &[],
    )
    .map_err(|error| {
        failure(format!(
            "legacy open failed: {}. {LEGACY_PATHS}",
            error.message
        ))
    })?;
    if !output.status.success() {
        return Err(failure(format!(
            "legacy open failed: {}\n{LEGACY_PATHS}",
            String::from_utf8_lossy(&output.stderr).trim()
        )));
    }

    let descriptor = super::descriptor(fs::read(frozen.path.join("environment.bytes"))?, &limits);
    // Unlike ordinary WAL create, an upgrade must claim an entirely new path.
    DirBuilder::new()
        .mode(0o700)
        .create(&destination)
        .map_err(storage_error)?;
    Log::create(&destination, &descriptor, state).map_err(storage_error)?;
    drop(owner);
    Ok(())
}

fn regular_file(path: &Path) -> io::Result<File> {
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK)
        .open(path)?;
    if !file.metadata()?.is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("nonregular legacy file {}", path.display()),
        ));
    }
    Ok(file)
}

fn copy_file(mut input: impl Read, path: &Path) -> io::Result<u64> {
    io::copy(&mut input, &mut File::create_new(path)?)
}

fn check_controller(environment: &mut File, executable: &Path) -> Result<()> {
    // The sorted v1 descriptor ends in the controller name and exact bytes.
    // Refuse a substituted executable before asking it to open the replica.
    let controller = fs::read(executable).map_err(storage_error)?;
    let name = b"server/controller";
    let mut entry = Vec::new();
    for bytes in [name.as_slice(), &controller] {
        entry.extend_from_slice(&(bytes.len() as u64).to_be_bytes());
        entry.extend_from_slice(bytes);
    }
    let mut stored = vec![0; entry.len()];
    if environment
        .seek(SeekFrom::End(-(entry.len() as i64)))
        .and_then(|_| environment.read_exact(&mut stored))
        .is_err()
        || stored != entry
    {
        return Err(failure(format!(
            "legacy environment descriptor requires the original controller executable. {LEGACY_PATHS}"
        )));
    }
    environment.rewind().map_err(storage_error)
}

// The complete-image decoder from main, with environment identity and exact
// descriptor verification delegated to the original controller's open.
fn decode_image<'a>(bytes: &'a [u8], limits: &Limits) -> Result<&'a [u8]> {
    if bytes.len() < OVERHEAD || !bytes.starts_with(MAGIC) {
        return Err(failure("invalid image format"));
    }
    let end = bytes.len() - 32;
    if Sha256::digest(&bytes[..end])[..] != bytes[end..] {
        return Err(failure("image checksum mismatch"));
    }
    let mut offset = MAGIC.len() + 64;
    for expected in [
        limits.message,
        limits.state,
        limits.response,
        (bytes.len() - OVERHEAD) as u64,
    ] {
        let n = u64::from_be_bytes(bytes[offset..offset + 8].try_into().unwrap());
        if n != expected {
            return Err(failure("legacy image limits or length differ"));
        }
        offset += 8;
    }
    if (end - offset) as u64 > limits.state {
        return Err(failure("image state limit"));
    }
    Ok(&bytes[offset..end])
}

fn failure(message: impl Into<String>) -> Error {
    Error::new("STORAGE", message)
}
