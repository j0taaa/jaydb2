# JayDB2 experiment agreement

These experiments are authorized for implementation in separate T3 Code
threads, branches and worktrees. Keep the implementations small and useful.
The coordinator owns cross-experiment integration and final acceptance.

## Starting point and boundaries

The common anchor contains main at `9b751fa` plus the existing CPU-worker and
demo inspection changes. Each branch records its exact base and prerequisite
commits. Preserve existing work. Do not merge experiments to main, publish,
deploy, or create PRs unless separately instructed. Commit finished work on
the assigned experiment branch. Do not delegate further work to agents.

Keep the pinned, unmodified official Bend 2.0.39 compiler, primary checker,
BendTT and emitted runtime. Do not weaken admission, replace a failed proof
with a final-state check, grant helpers special permissions, introduce
assumed final validity, or pretend the existing serial theorem proves a new
host protocol. Contract extensions need an explicit specification, proof
scope and honest integration assumptions. Retain all three canonical limits.

Every program access, including existence, keys and failed/filtered reads,
remains governed by administrator laws at every applicable prefix. Working
states may temporarily violate a stable-state invariant only when the
installed laws explicitly permit that situation. Success publication must
preserve all applicable stable laws. The bridge to actual processes, files,
bytes and publication remains explicit.

## Execution lifecycle

Use these events consistently: complete frame received, enqueued, selected
for service, authenticated against the applicable snapshot, admitted,
executed, complete proposal/response prepared and worker cleaned up,
durably committed when enabled, published/result ready, response emitted.
Error precedence, exact program/proof/argument/dependency binding and fresh
authentication remain mandatory. Never cache identity across earlier writes.

Keep ordinary operation semantics and the normal protocol compatible except
for explicitly documented opt-in extensions. Unknown programs, prepared
registration/invalidation and write-capable programs are exclusive. Do not
silently introduce retries or long-lived execution workers.

## Experiments

1. `experiment-baseline`: a small repeatable benchmark runner for tiny reads,
   writes, multi-row transactions, substantial computation, different state
   sizes, ordinary submissions, preparation and prepared execution. Check
   results, control state evolution, record revisions/toolchain/hardware/
   worker settings and repeated timing variability. Runtime inputs prevent
   accidentally benchmarking constant evaluation. External timing suffices.
2. `experiment-preprocessing`: remove redundant decoding/preprocessing and
   worker launches. Preserve malformed-input/error precedence, current
   authentication, source/proof identity, artifact integrity and no private
   state in compilation files. Preserve fresh worker isolation.
3. `experiment-persistence`: optional complete-state durable snapshots. All
   rollback-capable checks and cleanup precede the durable commit. Same-
   filesystem temporary image, file flush, atomic replacement and directory
   flush precede publication/acknowledgment. Stop serving on uncertain commit;
   never claim rollback after possible durable commit. Single directory owner,
   authoritative-image recovery, no silent reinitialization or fallback to an
   older acknowledged state. Preserve users and all application tables. Keep
   handles ephemeral. State a recovery preservation contract connecting valid
   initialization/publication, exact serialization, protected storage and the
   same frozen environment. Arbitrary laws need not be executable booleans;
   checksums are not validity or authorization proofs. No WAL/replay/history
   needed. The current environment hash includes the controller executable:
   exact-environment reopening is acceptable initially; document it.
4. `experiment-library`: optional ordinary Bend modules and reusable proofs.
   Extend existing accepted finite-list/continuation composition; do not
   require a general Action bind or compiler change. Cover typed values and
   canonical records, full signed-64-bit-safe arithmetic, injective composite
   keys, reads/projections/traversals, filtering/sorting/grouping/pagination,
   aggregates, conditional/batch writes, joins/relations, counters/sequences,
   unique/nonunique/composite ordinary-table indexes, explicit index/summary
   maintenance/rebuilds, law templates and proof composition. Deliver useful
   milestones and a documented exact feature inventory. Advanced range
   indexes may remain a documented later milestone; full text, geospatial and
   a query optimizer are excluded. Prove functional behavior under documented
   preconditions as well as prefix safety. Include restricted-user examples.
   Existing scalar storage and error semantics remain intact. Nat's native
   48-bit limitation must not narrow stored signed 64-bit integers. Pagination
   sees successive current snapshots; no historical-snapshot promise. Every
   helper states its actual accesses; no special index primitive or triggers.
5. `experiment-scheduling`: bounded FIFO frame queue and backpressure, with
   one coordinator owning publication/handles/delivery. Bound retained bytes
   and ready responses, not just item count. EOF and terminal framing errors
   must be ordered after earlier complete requests. Stop dispatch on channel
   failure, drain owned workers safely. No invented busy/error outcome.
   Initial execution stays serial; per-user fairness is deferred.
6. `experiment-timing`: optional monotonic elapsed service timing including
   authentication/checking/compilation/execution/durability, excluding queued
   waiting and delivery. One simple metric suffices. Optional soft per-user
   fixed-period quotas check after fresh authentication and before admission;
   charge authenticated attempts once after completion, including failures.
   Running requests finish, so overshoot is allowed and not time-bounded.
   Define accounting-period/restart semantics and a distinct explicit policy
   receipt/extension instead of inventing a technical failure. No CPU metering,
   reservations or hard cancellation. Coordinate dispatch semantics with the
   scheduling branch and persistence boundaries with its branch.
7. `experiment-concurrency`: contiguous queue-head batches of programs with
   checked, source-bound whole-program read-only certification, including all
   continuations. Bound worker/thread count and retained state/results. Pin a
   snapshot, authenticate normally and retain ordinary administrator proofs.
   Drain reads before exclusive work; later reads see the exclusive result.
   Never bypass a queued writer to fill/refill a batch. A client flag or final
   unchanged bytes alone is insufficient. Check unchanged successful state as
   defense in depth. Prepare/invalidate are barriers. Responses remain FIFO;
   do not dispatch an exclusive request until earlier emissions succeed. Stop
   dispatch on delivery failure; clean already-active reads. Extend the serial
   model and test deliberate schedules, credential changes and invalidation.
   No optimistic retries, fine-grained locks, write merging or version history.
8. `experiment-gpu`: optional real GPU execution using the pinned compiler,
   literal emitted C and explicit GPU calls. Build/seal the entire GPU/native
   bundle before preparation. Verify requested/actual backend, correct output
   and state, unavailable-device/missing-or-substituted-artifact/allocation/
   runtime failure behavior. Small GPU concurrency limit. Compare complete
   requests and small versus large workloads honestly. Check available NVIDIA
   hardware/CUDA locally; do not silently substitute a fake backend.
9. `experiment-idempotency`: optional ordinary-table receipt protocol with
   explicit laws. Key by authenticated principal and caller request ID; bind
   exact canonical inputs and a stable operation/version identity, not a
   prepared handle. Atomically publish the business effect and a small
   operation-specific immutable receipt/result. Same ID/input returns a
   permitted receipt, conflicting reuse refuses. Laws prevent forged/changed
   receipts and govern deletion. Initially forbid principal-ID reuse while
   relevant receipts remain rather than adding an incarnation subsystem.
   Precommit errors/limits leave neither effect nor receipt. Retention bounds
   protection; persistence adds restart survival. No automatic retries,
   background cleanup, generic response cache or separate receipt locks.
10. `experiment-bend-host`: replace the Rust controller with Bend, retain the
    official TypeScript/compiler/checker integration and runtime. Inventory
    required effects early. Base Process.run is text-based with mandatory
    timeout/output limits; it is not equivalent to current binary pipe/no-
    deadline semantics. Add the smallest documented native/TypeScript adapter
    needed for binary subprocesses, filesystem durability and other OS effects.
    Implement actual controller decisions in Bend, preserve all host behavior
    and connect proofs to those actual functions. Do not merely wrap the Rust
    executable or provide a separate unused model. Coordinate the final port
    after host contracts stabilize; do useful capability/implementation work
    meanwhile. State any remaining trusted effects honestly.

## Coordination and validation

All worktrees may share `/home/jota/projects/jaydb2/.tools` as an immutable
toolchain (an ignored `.tools` symlink is fine); do not alter pinned sources.
Use separate build/test/state/cache paths in each worktree. Run heavy proof,
native/integration tests and performance runs under the shared advisory lock
`/tmp/jaydb2-experiments-heavy.lock` (for example `flock ... make verify`).
This prevents competing benchmark runs and excessive parallel compilation.
Do independent source work while prerequisite branches are progressing.
Do not poll sibling threads or merge their in-progress commits; the coordinator
will provide accepted prerequisite hashes and integration instructions.

Each branch must contain `experiments/<topic>/REPORT.md` with: base/prerequisite
commits; exact supported behavior and CLI/library examples; changed contracts;
actual proof targets/functions and remaining assumptions (N/A for benchmark-
only changes); meaningful positive/negative/boundary tests and commands run;
performance observations/costs or explicitly unmeasured work; and remaining
limitations. Finish with clean committed work and a concise result containing
the head SHA and verification evidence. No staged-only or documentation-only
completion for implementation features. Do not declare success with a stub,
skipped core scenario or a vacuous safety statement. The coordinator will
review results, request repairs and check cross-feature integration.

Existing baseline checks include `make build`, `make verify-contract`,
`make verify`, `make test`, `make test-library`, and `make test-demo-web`.
Use checks appropriate to the change and add meaningful tests for actual new
boundaries. Process-kill recovery tests do not establish power-loss safety;
add a small fault-injectable storage model and state filesystem assumptions.
No test proves that hardware obeys its flush contract.
