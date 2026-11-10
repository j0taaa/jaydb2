# Service with three logical limits

Administrator configuration and dependencies are public. The chosen seed file
is private and participates only in initialization; public configuration may
not import it, including through another name or path to the same file.
Each custom administrator module name has one frozen source and dependency
graph. A seed helper or file alias that would reuse that name with a different
graph is rejected, even when its own text matches. `Configuration.bend` remains
the host-provided alias for the selected configuration file. A seed can use a
frozen public helper without keeping another local copy.

The active entry is `./jaydb2` → `server/main.rs` → `tools/service/stage.mjs`.
The host is Rust, admission and compilation are coordinated by Node, and each
compiled program uses the official Bend runtime. Python is not part of service
execution. Configuration contains only `message`, `state`, and `response`,
measured in canonical bytes. Equality with a ceiling is allowed. There is no
total-process memory budget, observer, or execution deadline.

## Call path

The optional [prepared-program extension](PREPARED_PROGRAMS.md) checks a
universal certificate and compiles once, then reuses an instance-local native
executable in fresh processes with current authentication, state, and arguments. Its controls and
receipts have a separate protocol boundary from the ordinary path below.

The framing reader queues complete original bodies. The checked native
`Dispatch.authentication` classifies ordinary versus prepared envelopes,
checks the full body length (including extension bytes), decodes before
fresh authentication, and enforces the empty handle-proof rule. Its tagged
metadata selects external admission or a prepared artifact; Rust copies the
checked source/context/arguments bindings to staging.

The generated entry calls `Worker.packet` (ordinary) or
`Worker.registered_packet` (prepared). Both decode the private published root
and retain it on early errors. Ordinary bodies use `Input.read_message`.
Prepared execution receives the actual live registration handle separately
from the original body and calls `Resolve.select`, then the same `Gate.begin`.
The gate authenticates against this root and invokes the generated admission
oracle. It starts exactly the admitted program with that authenticated context
and the actual arguments, or calls `Gate.early` without constructing a program.

For concrete admission the oracle matches the exact source/proof strings,
authenticated context and canonical arguments. Universal prepared admission
matches the frozen source/proof and specializes the checked universal proof to
the current context/arguments. Configuration is the same closed declaration at
every call site; the environment comparison is an additional integrity guard,
not an equality test for arbitrary configurations containing functions. T1
includes the binding of these declarations, certificate targets and actual
elaborated program to the immutable admitted Book. The oracle never elaborates
or approves new source at runtime.

The native loop drives `Execution.advance` / `Core.advance` incrementally.
On stopping, `Gate.finish` performs finalization, publication selection and
exact response framing. `Execution.decision` computes `Commit{root, bytes}` or
`Keep{bytes}` in checked Bend; its private encoding remains
`1 || frame(root) || response` or `0 || response`. Rust parses that sum, reaps
the child, completes rollback-capable cleanup, persists a Commit if enabled,
and physically replaces the published root/last-successful-response pair only
on Commit. It writes the returned response bytes unchanged. Packet framing and
size checks in Rust are integrity defenses, not a second finalizer.

Prepare/invalidate use the separately checked `Control.control` transition through
`ControlBridge.packet`, compiled at startup. The native controller checks the
current identity, full envelope, exact universal admission tuple, lifetime
freshness and bounded receipt before returning the registry delta. Rust stores
the opaque registry bytes, manages admitted artifacts and copies receipts.
`ControlTheorem` and the mixed service fold cover those decisions; physical
artifact integrity/cleanup and external process failures remain host duties.

The serial coordinator completes execution, cleanup, and publication, then
writes and flushes the response before selecting another request. Uncertain
publication terminates service without a response. Prepared registry mutations
remain inside the same exclusively owned service.
No identity is computed/cached by the framing reader.

Queue reservations include a body currently being read: at most 8 items and
`max(min(message limit, isize::MAX), 1 MiB)` body bytes, plus one header and one terminal slot.
With serial execution there is one additional active request of at most the message limit, and one
ready/emitting response subject to the existing logical response checks (or a
fixed canonical error). The published pair, proposal/worker intermediates,
prepared registry, allocator overhead and OS pipe buffers retain their existing
costs; this is not a total-process memory ceiling. All canonical uint64 message
limits remain valid; the accounting ceiling is not an upfront allocation. An
actual unallocatable body under the logical limit terminates as an ordered
technical transport failure without a false canonical limit response.

Clean EOF drains complete requests. Partial header/body, oversize declarations
and input IO failure become terminal events behind earlier complete frames;
only the coordinator may emit the canonical terminal input/limit response.
Input IO failure retains its fatal behavior after preceding responses. No
terminal event bypasses queued service. On output failure, no more work is
selected and a cancellation socket wakes the reader's polling/capacity waits;
the reader is joined before the service returns. Workers are already reaped
before response-ready. This adds no execution or delivery timeout.

Compilation directories receive code, proofs, and public admission data, never
private state. The seed participates only in initialization and is removed
before serving. Per-call state crosses pipes in RAM, never a temporary input
file.

## Ownership and failures

The Rust host owns each process and its pipes. Local threads feed input and
drain stdout/stderr concurrently to avoid pipe deadlocks. The host waits for
child exit and complete reading before accepting a proposal.

There is no DSO, lease, `dlclose`, or replacement runtime. Child exit
releases its resources. A child failure returns `failure` without publishing, and
the host can serve the next call. Uncertain ownership ends use of the instance
without repeating a potentially consumed operation.

The profile is a serial FIFO Linux CLI with trusted tools and host. Its default
volatile mode loses RAM data when the host dies. Optional complete-image
persistence is enabled explicitly:

```sh
./jaydb2 --configuration examples/access/Configuration.bend \
  --seed examples/access/Seed.bend --storage DATABASE --storage-mode create
./jaydb2 --configuration examples/access/Configuration.bend \
  --storage DATABASE --storage-mode open
```

Create requires a new directory with an existing parent; open requires the
authoritative snapshot and forbids `--seed`. A single owner holds an OS lock.
Every successful state proposal writes and synchronizes a complete temporary
image, atomically replaces the authoritative image, and synchronizes the
directory before RAM publication and response delivery. Errors from replacement
onward stop the instance with no response, since rollback may be false. Missing,
corrupt or incompatible images stop startup; no seed or older image is used as
fallback. Users and all tables survive; prepared handles do not.

Recovery requires the exact same environment, including actual controller
executable bytes. Protect the storage directory and preserve that executable
and its sources/tooling. Development databases are disposable; cross-build
compatibility and migrations are deliberately outside this feature. Recreate a
development database explicitly after changing its frozen environment. Process death tests do not establish hardware power-loss safety.

The Node helper uses only a public stack-size option, without an addon or Bend
change. The stage uses Clang 19 with `--no-default-config`; native programs
receive the official `--threads N --gpu off` options. CPU workers default to
the host's available parallelism, capped at 128 (one if detection fails).
The host's `--threads N` option accepts 1–128 and applies to all native stages,
including prepared execution. Each native process uses the selected budget.
Publication and response delivery remain owned by the coordinator.
Installation of these tools is part of the trusted environment.

Optional [administrator timing](SERVICE_TIMING.md) records monotonic elapsed
service time through cleanup and result readiness, before response delivery.
It changes no client responses or admission decisions. This integration has no quota policy.

## Verification and remaining host obligations

`proof/WorkerBridge.bend::worker_body_equals_ingress_composition` proves that,
for any final reference trace, finite unrolling of the actual worker adapter
produces exactly the Gate composition's output. It reuses
`ExecutionAdapter.finite_execution_reaches_exact_adapter_result`;
`worker_unified_equals_gate_composition` covers actual Resolve selection.
Halted paths use `Gate.early` and cannot resume. The generated checked Book
also proves its literal entry and Native iteration conversion/step equations.
Core's progress witness supplies the finite index; production has no fuel
limit and never replays prefixes. These lemmas connect the emitted decision
and bytes to Ingress/UnifiedCore under their existing validity and sound-oracle
premises, without assuming compiler or C-loop preservation as a Bend proof.

T1 remains official admission soundness plus exact source/target/Book binding.
T2 remains preservation by the official compiler, native runtime and foreign
loop. The remaining T3 plumbing obligations are:

1. Freeze the checked configuration, dependency/tool bytes and valid initial
   root; keep private root bytes separate from client inputs.
2. Frame complete original bodies with the specified bounds/EOF ordering;
   supply exactly one current root and the live registration/artifact binding.
3. Admit the exact checked tuple, compile the same immutable Book, validate
   artifact provenance and run a fresh worker with only its private proposal.
4. Collect complete output, reap workers and finish rollback-capable cleanup
   before publication; actual precommit technical failures keep the old root.
5. Obey Commit/Keep exactly, atomically publish the paired root/response, and
   write the returned bytes; delivery failure cannot undo a committed root.
6. Supply controls the unchanged current root, complete body, exact T1
   universal-admission tuple and prior opaque registry. Store only the returned
   delta/registry, retain allocated history, manage the corresponding artifact
   and write exactly the returned receipt; keep the root/response pair.
7. Preserve FIFO root feeding and timing/inspection noninterference. Optional
   durable storage and artifact cleanup retain their physical ordering and
   recovery obligations; prepared handles remain in memory.

`make test` rebuilds before native/integration tests. `make verify-contract`
and `make verify` check the inhabited executable Init/Core/Ingress/UnifiedCore/
Fold, wire and worker-bridge theorems with both official tools, including
causal negative controls for refusal publication and forged worker context.
The [proof guide](../../proof/README.md) maps their premises and the T1–T3
integration obligations. Native/integration tests check real compilation,
effects, persistence and responses; they do not prove T1, T2 or Rust/OS
correspondence.

## Rust helper pipe startup

Rust helper capture starts all three fallible scoped pipe threads before
launching a helper. Each waits on a bounded one-shot channel for its owned pipe.
Any thread-start failure or unwind drops the senders inside the scope, so all
started threads finish without a helper or compiler descendant ever launching.
A failed executable spawn also disconnects and joins those waiting threads.
After spawn, a guard retains direct-child ownership before pipe handoff. Normal
captures drain binary input/output/stderr concurrently and wait for the child.
Process-group behavior is unchanged; this is not a general process-tree
cancellation guarantee for arbitrary hard kills or aborts.

A pipe-thread startup failure retains the existing fatal policy after waiting
threads join; it cannot become a recoverable response or allow a later queued
write. Tests inject errors and unwinds at all three starts with a pre-exec launch
sentinel and a positive control, so they prove the helper never launched rather
than merely missing an asynchronously written marker. These tests support the
OS boundary without introducing a mechanized proof or an execution deadline.

The administrator inspection sequence is a modulo-2^64 diagnostic counter;
it wraps explicitly and does not identify semantic worlds, runs or proof times.

Host diagnostics are best-effort. A failed timing or inspection sink is disabled
before attempting its diagnostic, and failed stderr writes cannot suppress an
ordinary response, undo publication or turn an observer error into a panic.
