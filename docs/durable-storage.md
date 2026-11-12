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
consecutive and match slot parity; recover the newer. With one valid slot,
recover it: every protocol write leaves the current publication's blocks
untouched while writing its older/empty peer. Torn slots are ignored only when
another complete valid slot exists. Neither valid, wrong placement, stale/gapped
or tied valid sequences, checksum-valid incompatible images, bad geometry or
oversized files fail closed. Temporary/backup files never compete, and startup
never silently reseeds. Recovery synchronizes the authoritative file and
directory before serving, stabilizing a surviving unacknowledged write/rename.
A nonzero invalid peer is first overwritten with zeros and that clearing is
synchronized before any new request: otherwise a later torn write at the same
next sequence could resurrect an earlier failed candidate's retained checksum.
A crash during clearing may still recover that earlier unacknowledged candidate;
no request has been admitted yet, and the current valid slot remains intact.
There is no tail truncation or search for partially appended records. Prepared
handles and the last response remain instance-local. Exact immutable environment
binding and single-owner locking remain required. Old v1 images require explicit
recreation; migration/cross-build compatibility remain outside scope.

The physical trusted boundary is Linux/ext4 with 4096-byte filesystem blocks
(checked at open): successful `fdatasync` persists written data and any metadata
needed to retrieve it; successful file/directory `fsync` and atomic replacement
have their documented durability semantics, and the device honors flushes.
A slot overwrite must not damage previously synchronized blocks in the other
slot or expose stale allocation contents. No sector, filesystem-block or
multi-sector write atomicity is assumed. Unlike the old atomic-image protocol,
torn-slot detection now explicitly depends on SHA-256 rejecting incomplete or
mixed sequence/payload contents; undetected collisions are excluded. Checksums
are neither certificates nor authentication. Protected storage still excludes
malicious rewriting, unrelated media corruption, and hardware losing acknowledged
synchronized writes. Recovery cannot distinguish arbitrary later corruption of
the newest acknowledged slot from an interrupted overwrite under a broader
fault model. Rust/OS call-by-call refinement, byte framing, slot selection,
allocation and disk provenance remain T3 obligations supported by tests.

`proof/DurableCommit.bend` checks both the four-call replacement model and the
prepare/slot-write/data-sync model: success forces the candidate, safe failure
preserves the previous publication, and each modeled crash choice recovers a
state certified by the actual history transition. It does not prove checksum
injectivity, framing, syscalls or hardware behavior. Group commit could amortize
a sync across several requests if publication were batched and all acknowledgements
waited for that sync; the current serial host does not batch.
