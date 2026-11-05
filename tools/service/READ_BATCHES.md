# Certified prepared read batches

Start with `--threads 4 --read-workers 2` to allow two concurrent CPU read
requests. `--read-workers` defaults to 1, accepts 1..16, and cannot exceed
`--threads`. Each active read's native process uses floor(threads/read-workers)
CPU workers; exclusive requests use the full configured thread count.

Prepare a read with the explicit opcode 3 extension (Python
`prepared_frame(3, source, credential, arguments, proof)` or
`tools/client.py --prepare-read`). Execute/invalidate with existing opcodes 1/2.
Preparation still authenticates normally and checks the ordinary **universal**
administrator certificate and termination proof. It additionally checks:

```bend
law read_only:
  ReadOnly.Program(Client.program())
```

The client supplies `def B.read_only(ctx, args): (depth, evidence)` in the same
source-bound universal proof file. `src/ReadOnly.bend` is flattened and pinned
by hash during admission. `ReadOnly.Action(depth, action)` allows Finish,
Refuse, ReadCell, ViewExistence, CountRows and EnumerateKeys, covers **every**
S.Return continuation, and has no inhabitant at depth zero. `Program` requires
such a finite witness for all contexts and arguments. The witness does not
depend on database observations. Programs without this certificate, including
read traversals needing state-dependent depth bounds, retain ordinary exclusive
execution. `experiments/concurrency/Read{,Proof}.bend` is a complete example
against `examples/credentials`.

The coordinator selects a fixed group of currently queued consecutive certified
reads, stopping at the first barrier or worker bound. It never waits to fill or
refills a running group. Unknown handles, ordinary submissions, write-capable
prepared calls, preparation and invalidation are exclusive. Handle sniffing
provides only a scheduling hint: full canonical decoding, fresh authentication,
proof-field validation, sealed artifact validation and native execution still
run for every selected read on the same pinned snapshot. No identity is cached
across a write. Every native invocation remains a fresh, drained and reaped
process. Successful proposed state must equal the pinned state as an additional
check; returned states are then discarded.

The single coordinator emits in FIFO order. Read successes update the published
last-success response in that order. With storage enabled, the unchanged root
is already durable, so reads do not replace its image again. Writes still use
the durable publication boundary. All earlier read emissions must succeed
before an exclusive request starts. A write/flush failure stops dispatch and
joins every already-active read; there is no rollback or retry. Cleanup waits
for active certified computations rather than cancelling them at a deadline.

Retained work is bounded by the existing framing queue, at most N active bodies
and native pipelines, and at most N ready response frames. One host state is
shared by immutable reference. Native processes and their input/output pipes
may hold up to N copies of bounded state/response encodings. The bridge still
trusts the pinned compiler/runtime, OS process/pipe isolation, host-owned sealed
files and exact canonical transport. No claim is made that the pure theorem
proves these physical effects.

`proof/ReadBatches.bend` proves actual operation nonmutation, finite/all-prefix
state preservation, the Core incremental bridge, fresh-authentication
preservation, and heterogeneous frozen-batch/serial trace equality. Each model
call carries its own program and read certificate. Administrator authorization
continues to use the independent ordinary admission theorems. Rust tests
exercise completion ordering, barriers, bounds and failed output; native tests
hold two real checked worker processes concurrently with a test-only preload
adapter and verify writes, credential rotation, invalidation, failure, delivery
cleanup and persistent reopening. See the experiment report for actual checks
and results.
