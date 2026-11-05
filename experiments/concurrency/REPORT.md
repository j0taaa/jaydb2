# Conservative prepared read batches

## Revisions and prerequisites

Worktree/branch: `experiment-concurrency`. Common base
`5925c57febd978d44fa24000233647a59e7898a6`; original reference
`9b751fab3c7c349ff473a2d11a7133573b6c4df2`. Merged only coordinator-authorized
prerequisites:

- Preprocessing: `0f09c55dfff52fe10cd86b18a72a3241c5a92ad5`.
- FIFO scheduler: interface `d8ac16189df3869192581bffc5acad735226d512`,
  boundary fix `23f7bcb7e8b718288a7cad869215b8acee91b005`, real integration
  `0aeaa4569dcf164844e72fc368f07eae9f022446`.
- Shared admission fault-injection harness: cherry-picked only test fix
  `adad1b9ed9602af926cb3bb3935dab087985aca4` (no GPU feature).
- Persistence: stable publication callback
  `83a9f3703345c234fe3b14363e6e14e15cb88b80`, uint64 image-limit fix
  `6c6e494c081b3332d244900b14a6a9581249a4aa`.

The coordinator separately passed both official checkers for the byte-identical
`src/ReadOnly.bend` at `b6ef4a6681906859fdcdd4caf5b85b8fd318dcd8`; that
module/API acceptance does not imply acceptance of the full host protocol.
The ignored `.tools` symlink targets the immutable shared official toolchain.
No pinned compiler, primary checker, BendTT or emitted runtime was modified.

## Supported behavior and examples

`--read-workers N` opts into up to 16 concurrent CPU reads, defaults to 1, and
cannot exceed `--threads`. Exclusive native requests use `--threads`; each
active read uses floor(threads/read-workers) native CPU workers. For example:

```
./jaydb2 --configuration examples/credential-exchange/Configuration.bend \
  --seed examples/credential-exchange/Seed.bend --threads 4 --read-workers 2
python3 tools/client.py --prepare-read --code experiments/concurrency/Read.bend \
  --proof experiments/concurrency/ReadProof.bend --credential alice-token
python3 tools/client.py --handle HANDLE --credential alice-token --arguments 11
```

Opcode 3 is an explicit prepared-protocol extension: checked read preparation.
Opcode 1 executes any prepared handle and opcode 2 invalidates. Source, proof,
arguments, dependency and native-artifact binding remain exact. A read
registration requires the ordinary universal administrator certificate and
termination proof **plus** `Bindings.read_only : ReadOnly.Program(Client.program())`.
Both official checkers check the extra target; admission pins the predicate's
exact flattened source. A client flag, a source name, an unchanged result, or
a proof about only one observed path cannot grant read capability.

`ReadOnly.Operation` permits `ReadCell`, `ViewExistence`, `CountRows`,
`EnumerateKeys`. `Action(depth, action)` covers every `S.Return` continuation
and is uninhabited at depth zero. `Program` requires a finite witness for every
context and argument. The witness can depend on context/arguments, not on an
observation. This intentionally excludes state-dependent traversals lacking
such a bound from the parallel lane; their ordinary exclusive path remains
available. Existing errors and all three canonical limits are retained.

One coordinator selects only currently queued consecutive certified reads,
stopping at the first barrier or worker bound. It never waits to fill a batch
and never refills it. Unknown programs/handles, ordinary submissions,
write-capable prepared calls, preparation and invalidation are exclusive.
Candidate-handle parsing provides only a selection hint. Full ordinary
canonical decoding/authentication and proof-field checks run on the pinned
snapshot, followed by sealed-artifact checks and fresh native execution. No
identity survives a write. Reads complete before the next exclusive operation;
responses emit FIFO, and earlier emissions must succeed before exclusive work
starts. Failure stops dispatch and joins all already-started workers.

A successful returned state must equal the snapshot as defense in depth.
Successful reads still publish the new paired `Published.response` in FIFO
order. Errors/refusals leave the last-success pair intact. With storage enabled,
the unchanged root is already durable; the redundant disk replacement is
skipped. Exclusive requests retain `publish_with_ready` and fatal uncertain
commit handling. Prepared handles are ephemeral after reopen.

## Bounds, proof scope and trusted bridge

The existing queue retains 8 items and at most max(message-limit, 1 MiB) body
bytes, saturated at host representability. There are at most N active read
bodies/native pipelines. The host shares one state by immutable reference;
active inputs/native outputs may each retain a bounded state/response copy.
Returned states are discarded before results wait for FIFO delivery; at most
N bounded response frames plus the published last response remain ready.
At most N fresh child processes run concurrently, with total native CPU workers
at most `--threads`, N scoped host workers, three pipe-pump threads per active
child, and one framing reader. There are no long-lived execution workers.
Physical worker internals remain subject to environmental resource failures.

`proof/ReadBatches.bend` checks these actual targets/functions:

- `read_operation_cannot_change`: case analysis through actual canonical
  `Data.operate`, including address/schema/missing-row failure paths.
- `finite_prefix`, `prefix_preserves_state`, `finite_preserves_state`: all
  continuations and every mathematical execution prefix preserve state.
- `program_preserves_every_prefix`: specializes the universal finite witness
  to the actual context/arguments.
- `frozen_batch_refines_serial`: heterogeneous `Call` values carry independent
  `S.Program`s and per-entry `Certificates`; `frozen` and `serial` produce equal
  FIFO trace lists, including failure/filtered-read events.
- `reads_preserve_fresh_authentication`: state equality preserves actual
  `Data.authenticate` results within a read batch.
- `incremental_read_preserves_state`: connects state preservation to actual
  `Core.traverse/Core.start` using its existing prefix correspondence.

The extra certificate does not replace administrator laws: ordinary universal
admission and prepared-call specialization still cover all actual accesses,
prefixes and successful publication. The pure theorem does not prove Rust,
process scheduling, real bytes, files, pipes, delivery or disk flushes correct.
The trusted bridge includes the pinned compiler/runtime, exact canonical
transport, OS process isolation and reaping, protected host-owned sealed
artifacts, frozen configuration and the existing persistence filesystem
contract. Snapshot sharing is enforced by Rust borrows and coordinator barriers.

## Validation and costs

Completed locked gates (local TMPDIR
`.build/tmp`, shared lock `/tmp/jaydb2-experiments-heavy.lock`):

- `python3 -B tools/check.py proof/ReadBatches.bend`: both official primary
  and BendTT pass, including heterogeneous/Core/authentication targets.
- `cargo test --locked`: 32 host/read/scheduler/storage tests pass, including
  the accepted uint64 storage/queue boundary fixes.
- `make build`: release build passes.
- `python3 -B -m unittest tests.service.test_concurrency -v`: both native tests
  pass in 42.650 seconds, including real overlap and durable reopen.
- `make verify-contract`: both official checkers pass; historical/active
  contract hash checks pass.
- `make test-admission`: all 17 admission/verifier tests pass.
- `python3 -B -m unittest tests.service.test_end_to_end tests.service.test_prepared
  tests.service.test_preprocessing tests.service.test_scheduling -v`: all 9
  real service regressions pass (234.794 seconds).
- `node --test --test-concurrency=1 tests/admission/read-only.test.mjs`: both
  tests pass with all positive/negative subcases.

Additional completed checks:

- `cargo check --locked --tests`: pass.
- `cargo clippy --locked --all-targets -- -D warnings`: pass.
- Bounded official primary check of `proof/ReadBatches.bend`: pass, including
  heterogeneous/Core/authentication extensions.
- Bounded primary check of the staged native example/proof: pass.
- `ReadOnlyHiddenWrite.bend`: rejected specifically `Empty` versus `Unit` in
  `false`, covering a write hidden in an otherwise unreachable continuation.
- Quick aggregate primary check with a 20-second guard timed out without a
  verdict; no aggregate pass is claimed from that attempt.

The first native run stopped at setup authentication because the selected
`examples/credentials` seed uses `demo`. The fixture was corrected to the
free-law Alice/Bob seed in `examples/credential-exchange`; this did not change
production behavior. The corrected native rerun passes all scenarios.
The queued baseline service regressions also pass. No test is skipped.
The full `make verify` aggregate is not claimed from the bounded development
attempt; the new proof file and contract aggregate both passed their complete
official primary/BendTT gates.

New admission tests cover source/proof substitution, zero depth, fake predicates,
wrong targets, nonuniversal mode, and invalid independent administrator proof.
Host tests deliberately reverse completion, prove overlap with a barrier,
exercise active-read cleanup after delivery failure, queued-write exclusion,
credential rotation, invalidation, ordered terminal framing errors, last-success
pair bookkeeping and defense-in-depth changed-state rejection.
Native tests use the actual checked emitted-C executables. A test-only preload
adapter gates explicitly listed workers at stdin `fread`: two real child
processes must be alive before either is released. Tests pipeline reads and
writes, rotate credentials, invalidate handles, fail an overflowing native
computation, close the actual output pipe while reads are active, ensure the
queued write never launches, and reopen persistent state afterward. The pinned
compiler/runtime and emitted C remain unchanged by the schedule adapter.

No throughput/speedup benchmark was run. Costs include fresh authentication,
artifact hashing, fresh process startup, scoped host threads and FIFO waiting;
small reads may cost more than serial service. Timing/quota extensions are not
integrated here. Their completion timestamp must be taken in the read worker
immediately after cleanup, before ordered joins/delivery, with atomic quota
accounting rather than replaying completion stamps in FIFO order.

## Limitations

Only certified prepared CPU reads overlap. GPU-enabled work must stay exclusive
when GPU support is integrated. Reads without a universal finite continuation
witness remain exclusive. No optimistic retries, locks on rows, write merging,
version history, per-user fairness, deadlines or hard cancellation are added.
On failed delivery already-active computations finish and are cleaned up; this
cleanup has no wall-clock deadline. Full protocol correctness continues to
combine the checked pure model with the explicitly trusted host/effects bridge.
