# Complete-image persistence experiment

## Revisions and scope

Base: `5925c57febd978d44fa24000233647a59e7898a6` (original reference
`9b751fab3c7c349ff473a2d11a7133573b6c4df2`). Accepted prerequisite:
`0f09c55dfff52fe10cd86b18a72a3241c5a92ad5`, merged in `c681887`; the narrow
overlap preserves seed-free recovery and omits the redundant decode worker.
Storage interface milestone: `a95068f`. Initial integration: `46faca3`.

The Rust controller now supports opt-in synchronous complete-image persistence.
Working states remain private in RAM/native workers. Default operation remains
volatile. The three logical limits and public request/response bytes are
unchanged. All successful proposals, including unchanged successful states,
commit the entire canonical private-state encoding: every application table,
every row/column/value and all users/credentials. Refusals, errors, prepared
registration and invalidation do not write an image. Prepared handles and
compiled request artifacts remain instance-local and must be prepared again
after a restart.

```sh
make build
# Parent directory must exist; DATABASE must not exist, even as an empty dir.
./jaydb2 --configuration examples/access/Configuration.bend \
  --seed examples/access/Seed.bend \
  --storage DATABASE --storage-mode create --threads 1

# Stop the original owner first. No seed file is required or read here.
./jaydb2 --configuration examples/access/Configuration.bend \
  --storage DATABASE --storage-mode open --threads 1

# Existing default, no persistent state:
./jaydb2 --configuration examples/access/Configuration.bend \
  --seed examples/access/Seed.bend --threads 1
```

Both storage options must appear together. `--seed` is required for create and
volatile mode, and forbidden for open. Open never canonicalizes a seed path,
loads a seed module, evaluates `Seed.state`, or checks `Seed.initial_valid`.
It rebuilds/checks the public configuration and authenticating worker using the
pinned official tools, then loads the image. Seed-free recovery deliberately
does not try to execute arbitrary administrator laws as booleans.

## Storage and lifecycle contract

`Storage::begin(path, Mode::Create|Open)` acquires a nonblocking exclusive OS
file lock for the instance lifetime. `owner.lock` is never unlinked/replaced.
Create exclusively creates a mode-0700 directory, synchronizes its parent,
creates/synchronizes a mode-0600 owner file, and synchronizes the directory.
Open requires that directory, owner file and a regular authoritative
`snapshot`. The same directory cannot have two cooperating owners; kernel
descriptor cleanup releases ownership even on SIGKILL. The directory, parents,
owner inode and files must be protected from external modification/replacement.
The advisory lock does not protect against an administrator bypassing it.

`Database::publish(proposal) -> crate::Result<Vec<u8>>` is the reusable boundary
for scheduling/timing integration. Its input is the completed checked proposal
after worker reaping, full response preparation, state/response size checks,
artifact verification and request-directory cleanup. The normal serial path
calls `propose`, then `publish`. For successful state proposals it calls
`Storage::persist` before `Published::finish` replaces the RAM state/response.
`publish_with_ready(proposal, callback)` exposes the same boundary with a
callback immediately after the RAM pair is ready, before the final inspector
write. Timing can record its endpoint in this nonfallible callback and emit its
log afterward; final observer/client delivery delay is excluded. The ordinary
`publish` uses an empty callback. A host test observes the changed image and
absence of inspector bytes in the callback, then checks the published pair,
recovery and inspector output afterward.

The actual shared `storage::commit` algorithm is:

1. Serialize a complete image in memory and write a mode-0600, same-directory
   `.snapshot.tmp` with `write_all`.
2. Synchronize the temporary file with `File::sync_all`.
3. Atomically replace `snapshot` with `fs::rename`.
4. Synchronize the owning directory with `File::sync_all`.
5. Replace the RAM published pair, mark the result ready, then emit/flush the
   public response. Inspector delivery is optional and does not undo commit.

All rollback-capable proposal/response/cleanup work precedes step 1. Before
replacement is attempted, an I/O failure leaves the authoritative image and
RAM state unchanged and returns the ordinary technical failure frame. From the
replacement call onward, **any** error is `STORAGE_UNCERTAIN`, including a
rename error whose effect is unknown. It propagates as a fatal service error:
no response frame, no next request dispatch, nonzero process exit. There is no
claim of rollback after a possible commit. After successful directory sync,
process loss before publication or delivery can recover the new state without
the client having received a success. Clients must resolve such ambiguity at
the application level; this experiment performs no automatic retry.

An unsuccessful create may leave a directory with no committed image. Neither
open nor another create silently seeds it. The administrator must investigate
and explicitly choose a new directory for new initialization. No automatic
repair/reset command is provided.

The only recovery candidate is `snapshot`. Missing, truncated, oversized,
checksum-invalid, format-invalid, length-invalid or incompatible committed
images fail startup with no public response. `.snapshot.tmp`, `.old`, backups
or other directory contents are never used as a fallback. A leftover temp is
ignored on open and removed/recreated before a subsequent write. No WAL,
replay, persisted proof chain, migration, checkpoint process or history store
was added.

## Format and exact-environment compatibility

Version 1 is `jaydb2-image-v1\n`, the 64-byte hexadecimal frozen environment
identity, four big-endian u64s (message/state/response limits and payload
length), exact canonical state bytes, and SHA-256 of all preceding bytes.
Overhead is 144 bytes. Reads are bounded by the configured state limit plus
overhead before allocating the image; embedded lengths cannot request an
unbounded allocation. Both truncation and trailing bytes are rejected.

The environment identity includes public configuration/dependency bytes,
contract and runtime sources, host/admission/compiler tooling, Cargo inputs,
`server/main.rs`, `server/storage.rs`, and the **actual calling controller
executable bytes** read through `/proc`. Pinned compiler/checker identity is
also enforced by the existing admission pipeline. The private seed is not
part of the public environment. Equal configuration bytes in another path are
compatible; changed configuration/tooling or controller bytes are not. Tests
reopen with the exact same executable, reject an executable copy with one
appended byte, and reject a changed configuration. A rebuild, source change,
release/debug switch or fault-feature switch may require a new database.
There is no cross-version migration, portable deployment format or promise of
reproducible executable bytes. Preserve the exact executable and environment
needed to reopen an existing database.

SHA-256 detects accidental corruption and binds this format; it proves neither
authorization nor logical validity. A privileged attacker able to replace an
image and recompute its checksum is outside the protected-storage contract.
There is no malicious rollback detection or authenticated external storage.

## Recovery preservation and proof boundary

`proof/Persistence.bend` composes actual existing functions:

* `recovered_certified_publication_is_valid` derives recovered validity from
  certified initialization, `History.Sources`, and exact equality with
  `History.state`. `History.next` is the actual `Core.conclude` result and
  `History.step_preserves_validity` uses authenticated certification, actual
  traversal and faithful `Core.prepare`, rather than an assumed final-valid
  state. The semantic records are mathematical witnesses, not a persisted log.
* `complete_image_restores_actual_private_input_state` proves that exact image
  bytes pass the actual `Codec.decode -> Input.state_decoded -> State.decode`
  path with precisely the original state. It uses
  `CodecComplete.all_encoding_canonical_representable_and_decoded` and
  `Representation.transport_private_preserves_state`, with explicit canonical
  encoding, length, limit and protected-byte-equality premises.

Together these describe recovery validity as certified origin + exact
serialization/refinement + protected persistence, under the same frozen
configuration. A commit interrupted after replacement can choose either the
previous certified state or the new certified candidate; each is valid. A
successfully acknowledged commit must recover that image or a later certified
image, never an older acknowledged image. Missing/invalid storage may stop
recovery; validity preservation is not an availability claim.

The remaining explicit bridge assumptions are: the pinned official compiler,
checker, emitted runtime and native ABI faithfully implement the checked Bend
functions; Rust framing/serialization and worker provenance preserve those
bytes; the OS protects process memory and the owned directory; and a local
filesystem/device implements atomic same-filesystem replacement, file sync,
directory sync and persistence ordering as claimed. In particular, a synced
file followed by directory sync makes the complete new authoritative image
durable; before directory sync a crash can expose the old or new image (or
fail recovery), but may not silently resurrect an image older than the last
successful directory sync. Lock semantics must be valid for this filesystem.
Do not use network/untrusted filesystems without separately establishing
those guarantees. This is an additional host storage contract, not an
assertion that the old serial protocol theorem proves POSIX or hardware.

## Validation

All heavy commands use `flock /tmp/jaydb2-experiments-heavy.lock`; outputs,
native artifacts and test state stay in this worktree. `.tools` is an ignored
symlink to the immutable shared pinned official toolchain.

Checks completed at the storage-boundary checkpoint:

* `TMPDIR="$PWD/.build/persistence/tmp" cargo test --locked`: **12 passed**,
  including the actual result-ready/inspector boundary test.
* `flock /tmp/jaydb2-experiments-heavy.lock make test-persistence`: **7 passed**
  in 380.646 seconds. This run preceded the small result-ready callback addition;
  the callback received its own host boundary test afterward.
* `flock /tmp/jaydb2-experiments-heavy.lock python3 -B tools/check.py
  proof/Persistence.bend`: **both --check-only and --verdict passed**.
* `cargo fmt --all -- --check`, `git diff --check`, Python syntax compilation
  and `node --check tools/service/stage.mjs`: passed.

The final-source restart test (also adding real native-failure rollback to its
coverage) and existing volatile-mode integration/proof regressions are running
or queued under the shared lock. Their results will be recorded before final
completion. The checkpoint does not claim those pending commands passed.

Coverage added:

* Rust exact-image roundtrip; every-byte corruption and every truncation;
  environment/limit mismatch; real create/open lock and authoritative-only
  recovery; fatal publication suppresses output and later dispatch.
* A small fault-injectable `ImageIo` model runs the **same `commit` function**
  as real storage. Every operation is failed before and after its effect. It
  admits old/new recovery between replacement and directory sync, requires a
  synced temp before replacement, preserves the prior acknowledged image on
  safe failures, and requires the new image after successful completion.
* Real restart after acknowledged credential changes, SIGKILL after success,
  fresh authentication of both users, lost prepared handles, no seed file on
  open, both application tables and users, refusal rollback, and actual native
  worker failure after a private credential write with no image change.
* Missing/corrupt/incompatible authoritative images with valid temp/old files
  present; controller-byte and configuration mismatches; explicit create/open
  policy; real second-process ownership contention.
* A real filesystem temporary-path failure, followed by repair and a successful
  write, proves safe storage failures leave RAM and disk unchanged.
* A separately built `storage-fault-injection` feature supplies deterministic
  Unix-socket boundaries and EIO injection. It is absent from normal builds.
  SIGKILL boundaries: file sync, replacement, directory sync and RAM publication.
  EIO boundaries: before write, after file sync, before replacement, after
  replacement and after directory sync. Fatal cases queue a second request and
  assert zero public bytes, no later effect and successful subsequent recovery.
  At SIGKILL boundaries, tests verify no live child or request staging directory
  remains before durable work begins.

Process death tests do not establish power-loss safety. The model exposes the
flush/rename assumptions, and no test proves hardware honors its flush contract.

## Costs and limitations

Persistence serializes/hashes/writes O(state size) per successful request and
performs one file sync and one directory sync before publication, including
read-only successes. Startup still rebuilds two official native programs.
No throughput/latency or power-loss benchmark has been measured. The state
limit still bounds payload size; configured bounds and RAM/OS failures can
stop the process. Limits are logical byte bounds, not physical memory bounds.
The platform is Linux/Unix (including `/proc`, advisory locks and directory
sync); no Windows portability is claimed. The Rust standard library in the
tested toolchain provides `File::try_lock`. State remains in a single local
image; there is no backup rotation, migration, encryption, corruption repair,
receipt/idempotency implementation or multi-owner service. The image contains
private data and credentials and requires the same administrator protection
as the server process. A lost response remains ambiguous by design.
