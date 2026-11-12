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
Prepared execution receives the latest unchanged registry bytes from the
checked controller separately from the original body, decodes it with
`ControlBridge.decode_registry`, and calls `Resolve.select` over all live entries.
The generated oracle's `matches` compares resolved source/proof with the
artifact's frozen bindings under T1; `Worker.artifact_oracle` adds a second
integrity guard before that oracle can accept. Missing, removed, malformed or
mismatched entries emit a fixed denial with Keep. Rust's map locates the
executable file and can reject missing artifacts before the worker runs. Selection then
reaches the same `Gate.begin`.
The gate authenticates against this root and invokes the generated admission
oracle. It starts exactly the admitted program with that authenticated context
and the actual arguments, or calls `Gate.early` without constructing a program.

For concrete admission the oracle matches the exact source/proof strings,
authenticated context and structural arguments. Universal prepared admission
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
the returned registry bytes, manages admitted artifacts and copies receipts.
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
Every successful proposal whose canonical state bytes differ from the current
published state writes and synchronizes a complete temporary image, atomically
replaces the authoritative image, and synchronizes the directory before RAM
publication and response delivery. An identical state reuses the already durable
image; it still publishes the checked Commit root/response pair in RAM. The image
contains the immutable environment identity, limits, canonical state and checksum,
with no separate per-request response, sequence or prepared registry. Application
idempotency receipts are ordinary rows within that state, so creating or changing
a receipt still requires the full durable commit. The last response and allocated
handle history are instance-local and are not recovered after restart. Open
synchronizes the validated authoritative file and directory once: the previous
process may have died between rename and directory synchronization. Errors from
replacement onward stop the instance with no response, since rollback may be false. Missing,
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
`DispatchBridge.dispatch_denials_equal_ingress_unified_early` proves that every
Dispatch tag-0 reply has the exact bounded early-response bytes and unchanged
root in the Ingress/Unified composition. Dispatch and Worker share private-root
and body decoding. `CertifiedWorker.checked_prepared` covers the literal prepared
packet and its real registry; `WorkerDecision.completion_emits_exact_decision` states exact
Keep/Commit correspondence with the publication path and next root/bytes.
Halted paths use `Gate.early` and cannot resume. The generated checked Book
also proves the Native iteration conversion/step equations.
Core's progress witness supplies the finite index; production has no fuel
limit and never replays prefixes. These lemmas connect the emitted decision
and bytes to Ingress/UnifiedCore under their existing validity and sound-oracle
premises, without assuming compiler or C-loop preservation as a Bend proof.

The generated `generated_oracle_sound` law supplies the logical oracle premise.
T1 retains official checker soundness, exact source/Book/artifact binding and
the source/purity audit.
T2 remains preservation by the official compiler, native runtime and foreign
loop. The remaining T3 plumbing obligations are:

1. Freeze checked configuration, dependency/tool bytes and the checked initial
   root; keep private state separate from client input.
2. Frame bounded complete original bodies with the specified EOF ordering;
   supply the current root to the checked decoder/controller.
3. Admit exactly the tuple selected by checked dispatch; compile and load the
   same immutable checked Book and preserve its context, arguments and proof.
4. Run a fresh private worker through the checked gate/advance/finalizer and
   native loop, without publication capability.
5. Collect complete output, reap children and finish rollback-capable cleanup.
   Forward admission/other observed error codes/current snapshots to the checked
   controller; denial-executable/transport failure retains the fixed technical
   fallback. Memo hits forward checked bytes for the exact observed code.
6. Obey Commit/Keep exactly and atomically publish the paired root/response;
   feed the resulting root to the next request.
7. Forward the latest controller-emitted registry bytes unchanged, supply the
   exact T1 admission tuple to controls, install only checked deltas, preserve
   allocation history, and manage the matching artifacts. Physical map/integrity
   checks must prevent execution of an unavailable or changed artifact. Cache
   only checked replies by exact observed code; prefill both prepared codes at
   startup. `HostErrorReplyTheorem` states their independence from root/last/registry.
8. Deliver exactly the returned bytes; delivery failure cannot undo a commit.
   EOF/shutdown between requests closes the channel without a transaction.

FIFO scheduling and timing/inspection must preserve these obligations.
Durability and recovery retain their separate physical assumptions; handles
remain in memory. Registry bytes are unauthenticated: stale or fabricated
bytes can break invalidation and handle/program correspondence. Universally
certified execution under T1 and generated source/proof matching still applies.

Error-code classification and response construction execute in the existing
checked native controller. Its private metadata is a canonical text value
containing the exact observed error code, distinct from the four-text prepare
metadata list; the remaining packet contains the latest registry and current
root, with an empty body. `ControlBridge.run` calls `Control.host_error`, which
uses the total table in `contract/HostErrors.bend` and `Control.finish`'s denial.
`HostErrorReplyTheorem` proves bounded canonical framing and preservation of
root/last-response/registry. The 17 named admission codes map to `certificate`;
all other strings map to `failure`, including `HOST_COMPILE`, `HANDLE` and
`PREPARED_INTEGRITY`. Pure admission's failure code is preserved; a worker-check
failure after successful pure admission remains `HOST_COMPILE`. Native-build
errors (`phase: compile`) follow acceptance by both checkers, skip pure
rechecking and report `HELPER` (also `failure`).

Rust sends each exact observed code unchanged and memoizes only checked Keep
response bytes by that code. Startup prefills `HANDLE` and `PREPARED_INTEGRITY`
separately and fails if either checked denial cannot be obtained.
`HostErrorReplyTheorem` states that output equals
`Messages.error(HostErrors.status(code))` for every root/last/registry, so the
memo remains valid for later roots under immutable instance limits. Prepared
map/integrity denials use these entries without another child. Other codes,
including `HOST_IO`, use their own entry or the checked controller.

The status table and reply construction moved into checked Bend. Detection of
handle-map misses and integrity failures, passing the exact observed code,
cache forwarding and the technical fallback remain trusted within the
corresponding host duties. The proof guide reorganizes these duties into eight
items; it does not claim a reduction from eleven to eight trusted duties.
The 17-code certificate table is a contract specification, with no proof that
it equals the Node tools' proof-rejection codes (`ORACLE_PROOF`, `ADT` and
`INSTANCE_MATCH` map to `failure`). A literal-code inventory test guards
against new codes without deliberate classification.

If the denial controller or its transport fails, Rust keeps the root and emits
the fixed technical fallback with an explicit stderr diagnostic. The fallback
is never memoized. Ordinary success and healthy prepared execution retain
their process/check counts; startup performs two checked denial computations.

Prepare/invalidate replies come from the controller under `ControlTheorem`,
not the worker's denial branch. The Dispatch bridge compares tag-0 output to
Ingress/Unified; it does not prove correspondence with controller replies.
`ControlRegistryBytes.control_output_registry_decodes` connects successful
controller registry serialization/framing to the exact decoder used by the
prepared worker, subject to representable lengths and octet blocks.

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

## Admission and artifact release

The compiler preflights the import-only pure root and verifies that every pure
module has exactly the executable Book's bytes, role and policy. A successful
full Book checks all these declarations in both official modes once. If worker
checking fails, the separate pure check distinguishes a rejected client
certificate from a host wrapper failure. Native-build failures need no recheck.

Service compilation overlaps only independent work. The primary checker first
elaborates every declaration, then the official Safe translator consumes those
checked trees and fixes the complete BendTT input. The original BendTT process
runs concurrently with C emission from that same private Book and Clang
(`-O0` for ordinary requests, `-O2` for reusable/startup workers). The semantic
seal is checked after translation immediately before C emission; it covers
checked runtime bodies as well as source terms. The official emitter transforms
its input Book under T2. A second seal covers its resulting private state and
is checked before admission returns, detecting subsequent edits. No client
source is reread, no verdict is cached, and Safe's permitted symbolic constants
retain the existing treatment. The foreign C snapshot is validated before use.

C, the executable and their hashes are provisional during that overlap.
Both paths must settle and their children exit before admission returns a
handle. `compile.mjs` withholds successful C/native receipts until both checkers
accept and the seal and artifact hashes match. `stage.mjs` validates those
hashes before releasing a program path; Rust then copies the released ELF into an owned memfd, seals it, verifies
the seals and hashes those sealed contents before executing that exact fd.
It relies on kernel immutability thereafter rather than rereading staging files
on every call (see [native execution](../../native/SIMPLE_RUNTIME.md)). A
checker/build/binding failure releases no worker. On every reported failure,
the checking/build paths have settled and provisional files are discarded.
Uncatchable V8 OOM or a hard kill of the direct child can orphan kernel/Clang
processes or leave provisional files. T1 rests on withheld receipts and seal/hash
checks, not on cleanup. Checker and seal failures take precedence over a
simultaneous build failure. Public response statuses and publication behavior
are unchanged.

With `JAYDB_BENCH_TIMING`, `bendtt_translate_check` records the observed wall
span of translation and the kernel child; it overlaps `c_emission` and
`c_compilation` and must not be added to them or subtracted with them from the
round trip to infer an exclusive remainder. Child completion can be observed
after synchronous C emission yields the Node event loop. `admission_total`
remains the inclusive wall time of admission/build. Staging, worker, cleanup
and publication hooks retain their original boundaries.
