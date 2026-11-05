# Scheduling experiment

Base: `5925c57febd978d44fa24000233647a59e7898a6` (original reference
`9b751fab3c7c349ff473a2d11a7133573b6c4df2`).
Queue-interface milestone: `d8ac16189df3869192581bffc5acad735226d512`.
Canonical-limit review fix: `23f7bcb7e8b718288a7cad869215b8acee91b005`.
Accepted preprocessing prerequisite: `0f09c55dfff52fe10cd86b18a72a3241c5a92ad5`,
merged as `9e46f44`; it removes redundant decode compilation/execution while
retaining fresh actual Input.analyze authentication.

## Supported behavior and contracts

The ordinary CLI, canonical frames, three logical limits and prepared controls
are unchanged. Example:

```sh
./jaydb2 --configuration examples/access/Configuration.bend \
  --seed examples/access/Seed.bend --threads 1
```

The host now reads ahead through one bounded framing thread. The reader owns
no database, handles or output. One serial coordinator owns all database service, handle operations, publication and output.
It selects FIFO work, executes with fresh authentication against current state,
obtains a complete proposal after helper cleanup, publishes, then writes and
flushes one response before selecting again. No retries or busy outcome.

`server/scheduling.rs` exposes `QueueBounds`, `FrameInput`, `PollInput`,
`FrameQueue::{start,select,close}`, `FrameEvent`, `InputEnd`, `SerialService`
and `coordinate`. Service start/selection is immediately before `execute`;
its return means proposal/response preparation and worker cleanup are complete.
Successful `publish` return is response-ready; `publish` returns the existing
crate `Result<Vec<u8>>`, so a fatal/uncertain commit can stop without emission
or later dispatch. Ordinary proposal errors still become canonical responses.
Handles stay exclusively within the coordinator-owned service.

Clean EOF, partial headers/bodies, oversize frames and read failures are queued
terminal events after all earlier complete frames. The reader never emits a
response. Unknown frame extent terminates input without consuming a body or
attempting resynchronization. An output write/flush failure stops selection;
published state is not rolled back. Reader cancellation wakes both capacity
waits and descriptor polling; cleanup joins it even when client stdin is open.
Workers remain synchronous and freshly spawned, drained and reaped by capture.

## Retained work and limits

Let M be the canonical message limit, R the response limit, and
A = min(M, isize::MAX), B = max(A, 1 MiB). Queued plus reader-reserved
bodies retain at most B bytes
and 8 items (empty frames count); reserve before allocation and body reading.
There is at most one 8-byte header and one fixed terminal slot. Selection
releases capacity: one additional active body of at most A bytes is owned by
the coordinator. Total retained framing bodies are at most B + A bytes and
nine requests, plus the fixed terminal event. There is at most one
ready/emitting response, bounded by
max(R + 8, largest fixed error frame); Published also retains its last success
response and state as before. No multi-response backlog exists. Queue metadata,
allocator overhead, OS pipe buffers, active transport/metadata copies,
current/proposed state, compilation files,
prepared artifact registry and existing worker stdout/stderr captures are
outside the framing-body bound. This is not a total-process RAM guarantee;
worker intermediates and prepared registry were not globally bounded before
and remain unchanged. Logical limits are never repurposed as a busy status.
All canonical uint64 message limits remain valid at startup. A declared body
above the logical limit still produces limit; an actual unallocatable body
within that limit terminates as HOST_TRANSPORT, ordered after complete frames,
without a false canonical limit response. Allocation is attempted only for
the actual frame via fallible reservation, never for the accounting ceiling.

## Verification and proof scope

Current host validation: `cargo test --locked` passed all 17 host tests;
`cargo clippy --locked --all-targets -- -D warnings` passed; `cargo fmt` applied.
New deterministic tests cover body-byte and empty-frame item backpressure,
exact boundaries, clean EOF, every partial-header length, partial bodies,
oversize/u64-max declarations, interrupted/fragmented reads and read failure,
controlled execution/cleanup/delivery gates, ordered read-ahead terminal events,
fatal publication, zero/partial writes and flush failures, and cancellation
with input open at header/body/capacity waits. No-large-allocation regressions
accept small/empty frames under a uint64-max canonical limit, and reject actual
unallocatable declarations as ordered technical transport failures.
Existing host tests exercise
publication rollback and real shell-child pipe draining/reaping.

No new mechanized queue theorem is claimed. Existing Bend serial laws and
prepared normalization proof remain unchanged, conditional on their published
integration assumptions. The new framing-to-serial-service refinement is a
host implementation contract supported by tests and review; the old theorem
does not prove threaded Rust, descriptor cancellation, or this FIFO adapter.
A complete formal model of host scheduling is outside this implementation.
The accepted preprocessing prerequisite adds
`proof/Preprocessing.bend::gate_preserves_exact_output` and
`single_pass_preserves_exact_output`, establishing pure exact-byte equivalence
of the removed decode gate with the actual authenticate-pre route; they do
not prove this queue or OS/compiler behavior.

Heavy-lock real checks completed:

```sh
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'export TMPDIR="$PWD/build/tmp"; make build && python3 -B -m unittest tests.service.test_scheduling -v' > build/scheduling-integration.log 2>&1
```

Release build and all 3 real CLI tests passed (86.797 seconds for the tests).
Covers pipelined ordinary transactions with changing credentials, malformed
complete frames, fresh authentication, prepared registration/execution/
invalidation, and EOF draining queued controls. Separate terminal cases put
clean EOF, partial header, partial body or oversize declaration after a real
successful transaction and a complete invalid request. Closed-output test
keeps stdin open, observes exactly one admission despite queued successors,
and verifies owned artifacts disappear.

- Existing service regressions and contract/preprocessing proof validation are
  queued under the same lock; their results will be recorded below.

Temporary/build/log/state paths are under this worktree (`build/tmp`,
`target`, `build/scheduling-*.log`); `.tools` is an ignored symlink to the
immutable official toolchain. No pinned tool or runtime was modified.

No throughput/latency benchmark was run. Integration-test duration includes
initialization and real checking/compilation and is not a performance claim. One
reader thread, mutex/condition-variable synchronization and poll/read syscalls
are added. No parallel execution, fairness, quotas, timing or persistence is
implemented by this branch. A blocked output or nonreturning worker still has
no deadline; cancellation starts only after an observed output/fatal failure.
