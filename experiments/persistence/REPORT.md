# Complete-image persistence experiment

## Revisions and scope

Base: `5925c57febd978d44fa24000233647a59e7898a6` (original reference
`9b751fab3c7c349ff473a2d11a7133573b6c4df2`). Accepted prerequisite:
`0f09c55dfff52fe10cd86b18a72a3241c5a92ad5`, merged in `c681887`; the narrow
overlap preserves seed-free recovery and omits the redundant decode worker.
Storage interface milestone: `a95068f`. Initial integration: `46faca3`.
Tested result-ready callback checkpoint: `83a9f37`. Logical-limit boundary
repair: `6c6e494` (image-header overhead saturates instead of narrowing the
u64 state-limit domain).

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

The current development databases are disposable and there are no deployed
users requiring cross-build compatibility. Exact-environment reopening is the
intended policy for this experiment, not a pending acceptance requirement. No
backwards-compatibility layer, migration framework or portable upgrade format is
planned as part of this change. After changing the executable, configuration or
tooling, create a fresh database explicitly. To reopen an old development image,
retain its matching executable and frozen environment. The existing identity
check remains because it binds recovery to the established validity assumptions.

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
The runs used official Bend 2.0.39 and its pinned primary checker/BendTT/runtime,
Ubuntu Clang 19.1.1, and rustc 1.98.0. Persistence integration workers use one
CPU thread; existing volatile integration tests retain their existing settings.

Completed checks, with tested revisions distinguished explicitly:

* `TMPDIR="$PWD/.build/persistence/tmp" cargo test --locked`: **13 passed**
  after the limit repair, including the actual result-ready/inspector boundary
  test and real create/reopen at the maximum u64 logical state limit.
* `flock /tmp/jaydb2-experiments-heavy.lock make test-persistence`: **7 passed**
  in 380.646 seconds. This was the working tree based on `c681887` with the
  storage-source environment binding and new test additions, before the
  callback/native-failure-test additions committed in `83a9f37` and before
  `6c6e494`. Its actual fault-controller SHA-256 was
  `980dfe3990834cdc0d744987b31397009fbdd269b21fea47f1051aeb46613a06`.
  It is not claimed as a full-suite run of either later revision. The callback
  and limit repair received their own actual host boundary tests afterward.
* `flock /tmp/jaydb2-experiments-heavy.lock python3 -B tools/check.py
  proof/Persistence.bend`: **both --check-only and --verdict passed**.
  That proof and its Bend source dependencies are identical to the ones
  committed in `83a9f37` and retained by `6c6e494`.
* `cargo fmt --all -- --check`, `git diff --check`, Python syntax compilation
  and `node --check tools/service/stage.mjs`: passed.

* The broader command, under the shared lock, ran `make build`,
  `python3 -B tools/check.py VERIFY.bend tests/proof/VERIFY.bend`, then
  `TMPDIR="$PWD/.build/persistence/tmp" make test-integration`: **build passed,
  both proof aggregates passed both official modes, all 6 integration tests
  passed** in 154.895 seconds. This release executable included `83a9f37`'s
  callback and preceded `6c6e494`'s storage-limit repair; its SHA-256 was
  `2ff14f49b715c0eab70b9cc26565694958ce241cafd5ae976a63ee48cdb0d8c8`.
  These are volatile-mode regression results, not a rerun of the persistence
  fault suite on the limit repair. The new limit is checked by the 13-test
  final-source host suite above.

* **Final-source gate on `6c6e494`: passed.** Under the shared lock,
  `cargo build --locked --release --features storage-fault-injection
  --target-dir .build/persistence/fault` passed, then the command below passed
  in 64.612 seconds with worktree-local TMPDIR. It includes the callback and
  limit repair and adds an actual native worker failure after a private write,
  asserting the authoritative image is unchanged. The rebuilt controller's
  SHA-256 was
  `d1ea30f203d518ca788ae681e13e29b9b70bc05b7dd62281fca9a636a7931d6e`.

  ```sh
  TMPDIR="$PWD/.build/persistence/tmp" \
  JAYDB_PERSISTENCE_BINARY="$PWD/.build/persistence/fault/release/jaydb2" \
  python3 -B -m unittest \
    tests.service.test_persistence.PersistenceTests.test_acknowledged_restart_credentials_handles_and_seed_free_open -v
  ```

An extra redundant normal release rebuild was canceled while still waiting,
at the coordinator's request to prioritize first feature gates; it is not
reported as a successful check. No running test was interrupted. The final
report-only commit changes no runtime/proof/test source from `6c6e494`.
No performance run, full `make test` (including the unrelated admission mock),
or hardware power-cut test is claimed.

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


## Independent audit runtime-policy repair

The audit also found inherited `BENDRTS` could request independent early-exit
options despite explicit CPU arguments. `Program.run` now clears it, matching
the GPU branch's existing policy. The accepted shared source change is
`b7e873cb8e3638de23313ff3655d0feedfa2e4e0`; test-only follow-up
`c39bebbd0a9b64380dd10cdeea9112b82b52d5fe` uses one immutable executable
launch fixture. This avoids a write/exec race seen as `ETXTBSY` in an earlier
parallel test run, without production retries or global environment mutation.

Post-repair evidence, using the common heavy lock:

- All **14** Rust host/model tests pass with no ignored tests; strict
  all-target Clippy and formatting checks pass. Evidence:
  `build/audit/runtime-policy-fixture.log`.
- A release rebuild and the real
  `EndToEndTests.test_native_runtime_options_are_owned_by_host` pass
  (**16.211 s**). It starts with inherited `--gpu-build --help`, performs
  an admitted ordinary credential update, prepares a universal program and
  executes it with current credentials.
- Validated `server/main.rs` SHA-256:
  `958535bc39bbc21f058c86f747348cf49233bbe83cddc1e979850087d7d76709`. Later report-only edits do not change that source.

This is a process-runtime boundary repair. The Bend admission/proof functions
and canonical request/state/response formats are unchanged; their previous
proof results are retained without claiming another full aggregate rerun.
The previous performance measurements, if any, remain measurements of their
recorded revisions; no benchmark was repeated for this repair.

## External-review follow-up: helper cleanup

The inherited `Scope::spawn` setup path could unwind before `Child::wait` and
join a pipe blocked on a still-running helper. `server/capture.rs` now owns the
child inside the scoped closure, uses `Builder::spawn_scoped` for fallible pipe
startup, and kills/reaps on early return or unwind before implicit pipe joins.
The original fatal startup-failure policy is retained after cleanup; no new
public receipt or retry is introduced. Staging freezes this module alongside
the other controller sources. The shared module is byte-identical across the
nine active Rust-host variants. Main and the baseline comparison host remain
unchanged; no experiment branches were merged.

All 17 Rust host/model tests, strict all-target Clippy, formatting and release
build passed on this branch. New tests cover an injected startup error and an
unwind at EACH pipe-thread start, blocked stdin/output, actual child reaping,
and the fatal public capture path. A real ordinary/prepared/current-authentication runtime-policy
regression also passed. No Bend source proof, compiler, checker or runtime
implementation changed, so their earlier proof results remain scoped to their
recorded revisions rather than being relabelled as rerun aggregate evidence.
