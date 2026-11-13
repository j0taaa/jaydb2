# Durable alternating complete-state slots

Durable storage uses two equal, initialized, block-aligned slots in the single
`snapshot` file (slot format v2). Each contains a complete canonical state image
and a 64-byte header: 16-byte magic, big-endian u64 sequence and image length,
then SHA-256 of the first 32 header bytes **and the entire image payload**.
The inner image retains its environment/limits/state checksum. Binding the
sequence to the payload is essential: a new header over an untouched stale
payload must never become a newer valid publication. Padding is not state.
Slot A holds even sequences and B holds odd sequences; sequences never wrap.

A routine changed-state commit opens the existing authoritative inode, checks
its expected length, seeks to the older slot, writes the complete new frame,
and calls `fdatasync` once. The latest durable slot is never overwritten by this
commit. Both slots were fully written (including zeros), allocated and synced
at creation or growth, so routine commits neither extend the file nor convert
unwritten preallocated extents. No directory fsync, file creation or rename is
needed per routine commit. Only after synchronization succeeds may RAM state
and response be published. Identical states reuse the durable publication.
Preparation errors are safe rollback. Once a slot write is attempted, all
write/sync errors are fatal `STORAGE_UNCERTAIN`, even before an observed effect:
no reply and no later dispatch, because a complete candidate may survive.

Creation and growth write a fresh complete two-slot `.snapshot.tmp`, `fsync` it,
atomically rename it over `snapshot`, then `fsync` the directory. The candidate
occupies its sequence-selected slot; the other is initialized with zeros.
Before replacement, errors are safe rollback. From replacement onward errors
are uncertain. Growth occurs only when a state image no longer fits a slot;
slots grow to the next 4096-byte boundary and never shrink during routine writes.
Only the currently needed frame blocks are rewritten/allocated in RAM; unused
padding left from a larger old image is ignored by sequence/length/checksum.
The physical authoritative file is bounded by twice the padded maximum image
plus header, independently of commit count. Logical limits apply to each state,
not the physical file. A u64::MAX logical limit still permits small files; no
maximum-size reservation is required. Growth temporarily needs one additional
complete candidate file. No periodic compaction or unbounded log is needed.

Recovery requires valid file geometry and bounds allocation by its actual slot
size and logical state ceiling. It checks both slots, including bindings of
any checksum-valid older slot. With two valid slots, their sequences must be
consecutive and match slot parity; recover the newer. A valid slot beside an
all-zero slot is also accepted. **By default any nonzero invalid slot stops
startup with `STORAGE_INVALID_SLOT`, naming its index (0/A or 1/B) and reason,
without modifying `snapshot`.** A torn unacknowledged write and corruption of
the newest acknowledged commit are indistinguishable without extra durable
state. Silently taking the older slot could lose an acknowledged commit.
Neither valid, wrong placement, stale/gapped or tied valid sequences,
checksum-valid incompatible images, bad geometry and oversized files also fail
closed. Temporary/backup/evidence files never compete, and startup never reseeds.
Old single-image v1 snapshots fail with `STORAGE_FORMAT` naming format v1 and
remain byte-identical, even with repair enabled. Explicit recreation is required;
migration/cross-build compatibility remain outside scope.

An operator who has investigated an interrupted commit after power loss, kernel
crash or **SIGKILL during a write** may explicitly reopen with:

```sh
./jaydb2 --configuration CONFIGURATION --storage DATABASE --storage-mode open \
  --repair-invalid-slot
```

Use the exact original executable/environment. Before clearing a nonzero invalid
peer, repair creates a new mode-0600
`snapshot.invalid-slot-INDEX.SERIAL.evidence` in the storage directory, copies
**every byte of that slot including padding**, fsyncs that file, then fsyncs the
directory. Existing evidence is never replaced. Failure at any of those steps
stops startup before modifying the snapshot. Partial evidence from an interrupted
copy is retained and a later attempt uses a new name; only the copy whose syncs
completed authorizes clearing. Evidence is diagnostic, never a recovery candidate.
**This flag may discard the newest acknowledged commit if invalidity came from
corruption instead of an interrupted in-flight write.** Preserve the database,
evidence and logs and assess that loss explicitly; the flag is not automatic
corruption recovery and never overrides incompatible bindings or bad geometry.
Evidence copies can accumulate across interrupted operator repairs; retain or
archive them under operator control.

After evidence sync, repair durably zeroes the invalid peer before its next
sequence can be reused. Otherwise a later torn write at that sequence could
resurrect an earlier failed candidate's retained checksum. A crash during clearing
can itself expose such a complete candidate in the crash-only model; no request
has been admitted yet and the selected valid slot remains intact. Recovery
synchronizes the authoritative file and directory before serving (subject to the
writeback-error caveat below), stabilizing a surviving unacknowledged write/rename.
There is no tail truncation or search for partially appended records. Prepared
handles and the last response remain instance-local. Exact immutable environment
binding and single-owner locking remain required.

SIGKILL is not a guarantee of an untouched slot. The host uses buffered
seek/write_all (not an atomic whole-slot pwrite); Linux's buffered write loop
can stop on a pending fatal signal after copying only part of a multi-page write.
The process then dies without completing write_all. Thus even host-only SIGKILL
can require explicit repair; a kernel crash or power loss can also tear writes.
The deterministic `during_slot_write` test splits the write to expose this case;
it does not measure spontaneous SIGKILL tearing or establish power-loss safety.
See Linux's [buffered write loop](https://github.com/torvalds/linux/blob/master/mm/filemap.c)
and [ext4 buffered write path](https://github.com/torvalds/linux/blob/master/fs/ext4/file.c).

The physical trusted boundary assumes Linux/ext4 semantics with 4096-byte
filesystem blocks. Only the 4096-byte `f_frsize` is checked at open; ext4 and its
durability semantics are an operator assumption (other filesystems can pass that
size check). In a healthy writeback epoch, successful `fdatasync` persists
written data and metadata needed to retrieve it; successful file/directory `fsync` and atomic replacement
have their documented durability semantics, and the device honors flushes.
A slot overwrite must not damage previously synchronized blocks in the other
slot or expose stale allocation contents. No sector, filesystem-block or
multi-sector write atomicity is assumed. Unlike the old atomic-image protocol,
torn-slot detection now explicitly depends on SHA-256 rejecting incomplete or
mixed sequence/payload contents; undetected collisions are excluded. Checksums
are neither certificates nor authentication. Protected storage still excludes
malicious rewriting, unrelated media corruption, and hardware losing acknowledged
synchronized writes. Strict recovery refuses detected invalid slots even outside that crash-only
model; explicit repair accepts the acknowledged-commit loss risk described above. Rust/OS call-by-call refinement, byte framing, slot selection,
allocation and disk provenance remain T3 obligations supported by tests.

## Writeback-error recovery procedure

Linux [errseq](https://www.kernel.org/doc/html/latest/core-api/errseq.html)
tracks writeback errors using sampled cursors; an error already reported to the
failed process need not be reported to a newly opened file. After a sync failure,
a restart without reboot can read checksum-valid page-cache bytes that were never
persisted, and a later successful fsync need not retry those failed writes.
Recovery's buffered reads and sync therefore do **not** establish disk provenance
in that situation. We document this limitation instead of treating advisory
cache eviction as a durability proof; no O_DIRECT recovery path is implemented.

After EIO or another actual writeback/sync failure causing `STORAGE_UNCERTAIN`
(or a recovery sync failure), stop service and preserve diagnostics/storage for
investigation. Fix the device/filesystem fault, reboot to eliminate the suspect
page-cache epoch, and inspect/recover the on-disk snapshot with the same executable
and environment before serving again. Reboot does not repair lost bytes: strict
open may refuse, requiring restoration from a known durable backup or an explicit
loss decision using `--repair-invalid-slot`. Do not repeatedly restart or use
that flag to bypass a sync failure. Test-injected EIO at named hooks simulates
control flow, not a real kernel writeback-error epoch.

`proof/DurableCommit.bend` checks both the four-call replacement model and the
prepare/slot-write/data-sync model: success forces the candidate, safe failure
preserves the previous publication, and each modeled crash choice recovers a
state certified by the actual history transition, conditional on recovery
returning a state (strict mode may refuse). Its operator-repair model gates clearing
on explicit authorization and both evidence sync successes. It does not prove checksum
injectivity, framing, syscalls or hardware behavior. Group commit could amortize
a sync across several requests if publication were batched and all acknowledgements
waited for that sync; the current serial host does not batch.
