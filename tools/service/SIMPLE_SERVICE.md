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

## Checked migrations

```sh
node --stack_size=65536 tools/service/stage.mjs migrate WORKDIR \
  OLD_CONFIG_OR_ENV NEW_CONFIG MIGRATION BEND_SOURCE BENDTT
```

Use a fresh private work directory and the pinned Bend source and bendtt paths.
Pass the active frozen environment directory as `OLD_CONFIG_OR_ENV` for a
published database. A configuration file is also accepted for standalone builds.
`NEW_CONFIG` is a configuration file. The JSON result gives the executable
`program`, the new `limits`, and the frozen `newEnvironment` directory.

The migration file defines `migrate(s: D.State) -> D.State` and `preserves(s,
valid)` with the type `S.Satisfies(New.config(), S.Stable{migrate(s)})` given
`valid: R.Valid(Old.config(), s)`. Import the old configuration from
`./Old/Configuration.bend` and the new one from `./Configuration.bend`. Old
administrator helpers are under `Old/`, and the new graph uses its usual paths.
Both graphs share the same repository contract and runtime modules. The new
graph reserves `Old/` and `Migration.bend`; the migration file can import the
frozen graphs and repository modules. The generated Book checks the proof
against the same migration function it runs and requires both official checkers.

Run the executable with the complete old canonical state on stdin, then close
stdin. Stdout is `1 || new canonical state` after the structure and size checks,
or `0 || framed error response`. Invalid result structure gives `data`, an
oversized result gives `limit`, and an undecodable old state or invalid new
configuration gives `failure`. The caller supplies an old state that satisfies
the old stable laws. The task example in `applications/tasks/migrations/` adds
an optional integer priority. Package its new configuration with the existing
task application's `Policy.bend`.

## Call path

The [prepared-program extension](PREPARED_PROGRAMS.md) checks a universal
certificate at registration. The host starts one worker per handle on its
first call and reuses it until invalidation or failure. Ordinary calls still
check and compile each concrete certificate and run a one-request worker.

The host loads the canonical initial state into an indexed snapshot. A checked
startup executable exports the configuration's schema, and the host checks
that the exported schema and state fit the store's representation. The
framing reader queues complete original bodies. Concrete admission and
controls use checked `Dispatch.authentication` with a projection containing
the table layout and the matching user, if any. Dispatch checks the envelope,
including its full length, and decodes it before authentication and admission.

The generated entry calls `Remote.packet` (ordinary) or
`Remote.registered_packet` (prepared). The prepared worker receives the latest
controller registry and original request body. It authenticates through the
host's credential index before looking up the handle, then checks that the
resolved source and proof match the artifact's frozen bindings. The concrete
oracle also compares the context and structural arguments with its admitted
instance. Both workers ask for data operations over private framed pipes.
The host applies those operations to a transaction on the current snapshot.

A worker final frame contains a tag and the exact framed response. Tag 0 keeps
the current state. Tags 1 and 3 both propose success, so the host checks the
candidate state's structure and credentials before checking its encoded size.
If those checks pass, tag 1 publishes the transaction and tag 3 forwards the
worker's response-check error. A malformed frame or worker failure discards
the transaction and returns `failure`. A subsequent call starts a replacement
worker for a failed prepared handle.

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
fixed canonical error). The published snapshot, proposal/worker intermediates,
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
the reader is joined before the service returns. Direct workers are reaped
before response readiness. Prepared workers are reaped when their handles
are invalidated or the service shuts down.

Compilation directories receive code, proofs, and public admission data, never
private state. The seed participates only in initialization and is removed
before serving. The full state stays in the host during calls.

## Ownership and failures

The Rust host owns each process and its pipes. The live worker protocol
alternates request, operation and answer frames through finalization. Startup
and admission helpers still use concurrent input, output and stderr capture.

The profile is a serial FIFO Linux CLI with trusted tools and host. Its default
volatile mode loses RAM data when the host dies. Enable write-ahead logging
explicitly.

```sh
./jaydb2 --configuration examples/access/Configuration.bend \
  --seed examples/access/Seed.bend --storage DATABASE --storage-mode create
./jaydb2 --configuration examples/access/Configuration.bend \
  --storage DATABASE --storage-mode open
```

Create requires a new or empty directory with an existing parent. Open
requires a valid checkpoint and forbids `--seed`. A single owner holds an OS
lock. Each accepted commit appends one atomic write-set record and synchronizes
the WAL before publishing the snapshot and delivering the response. This
includes an empty write set for a successful read. A background thread writes
a checksummed checkpoint every 256 commits when its queue has room. Recovery
loads a valid checkpoint, replays later records and truncates a torn WAL tail.
WAL I/O failures stop the service without a response. Users and application
tables, including any idempotency receipts, survive restart. Prepared handles
and their allocation history are instance-local.

Recovery requires the exact same environment, including actual controller
executable bytes. Protect the storage directory and preserve that executable
and its sources/tooling. Development databases are disposable; cross-build
compatibility and migrations are deliberately outside this feature. Recreate a
development database explicitly after changing its frozen environment. Process death tests do not establish hardware power-loss safety.

The Node helper uses only a public stack-size option, without an addon or Bend
change. The stage uses Clang 19 with `--no-default-config`; native programs
receive the official `--threads N --gpu off` options by default. CPU workers default to
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
   supply the current authentication projection to checked preprocessing and controls.
3. Admit exactly the tuple selected by checked dispatch; compile and load the
   same immutable checked Book and preserve its context, arguments and proof.
4. Run the checked live entry and answer each operation from the transaction
   with the corresponding `D.operate` result.
5. Collect and validate complete frames, retire failed workers and finish
   direct worker cleanup. Forward observed error codes to the checked
   controller; denial-executable/transport failure retains the fixed technical
   fallback. Memo hits forward checked bytes for the exact observed code.
6. Check the candidate state for every success proposal, log accepted write
   sets before publication, and use the resulting snapshot for the next request.
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
metadata list. The remaining packet contains the latest registry, the empty
authentication projection and an empty body. `ControlBridge.run` calls `Control.host_error`, which
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
is never memoized. Startup performs two checked denial computations.

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
hashes before releasing a program path; Rust retains its existing artifact
verification before a fresh worker launch. A
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
and publication hooks retain their original boundaries. With `--gpu`, checking
and building are sequential (no overlap), and the CUDA-only post-run artifact
rechecks fall inside `ordinary_worker` / `prepared_worker`.

## Experimental GPU programs

Opt in on Linux/NVIDIA with `--gpu 512`: integer corpus MiB from 64 through
4096; the default remains `--gpu off`. Initialization, authentication and the
checked metadata controller always use CPU. CUDA executions are exclusive and
serial per service instance, including read-only programs; administrators must
coordinate separate instances. The corpus setting does not change the three
canonical byte limits, and does not cap total device/driver memory.

Programs and proofs use the ordinary request or prepared protocol unchanged.
Use explicit `tree!(...)` calls in the client; parallel lets inside the called
function use the official device backend. The same bang program with `--gpu off
--threads 16` uses Bend's CPU worker pool. Without reachable bangs, opting in
does not establish that a kernel launched. With `--gpu`, every submitted or
prepared program is built with a mandatory official cubin prebuild, so without a
usable CUDA device (concurrent managed memory) admission itself fails (a
`HELPER` failure whose diagnostic starts with `GPU_BUILD:`), even for bang-free
programs. With a usable device, bang-free programs run on the CPU pool. A requested bang never silently falls back to CPU.

GPU admission waits for **both** official checkers on the sealed Book before
C emission, Clang or CUDA use. It compiles literal C with `/usr/bin/clang-19`,
`-DBEND_CUDA=1 -lcuda -lnvrtc`, using system headers in `/usr/include` and
libraries in `/lib/x86_64-linux-gnu` on the measured machine. It invokes the
official executable with `+RTS --gpu-build -RTS` before releasing a report or
registration; `nvcc` is not needed. The report binds source, executable and
`.gpu` hashes, backend and corpus setting, and records (does not pin) the
resolved `libcuda`/`libnvrtc` paths and SHA-256: these vendor libraries and the
`cuda.h`/`nvrtc.h` headers come from the host environment and are trusted, not
attested. Private executable/cubin files must be regular files and match before
each run and before accepting output; CUDA prepared execution rechecks all exact
sealed bytes after each exchange. The default CPU path keeps its original
pre-run checks, now also requiring the executable to be a regular file.
An official `bend: compiling the GPU program` notice fails even if rebuilt
bytes happen to match. Substitution, removal, incompatible artifacts and device
errors discard the proposal, preserving the current published/durable root.
Fresh preparation is required after incompatible device/toolchain changes.

For example, under the shared heavy lock after `make build`:

```sh
python3 tools/client.py --code experiments/gpu/Client.bend \
  --proof examples/access/ClientProof.bend --credential alice-token --arguments '"abc"' |
  ./jaydb2 --configuration examples/access/Configuration.bend \
    --seed examples/access/Seed.bend --threads 1 --gpu 512 |
  python3 tools/client.py --decode
```

For preparation, pass `--prepare --proof experiments/gpu/ClientProof.bend` to
the client and keep the same server session open; execute the returned handle
with `--handle HANDLE --credential alice-token --arguments '"abc"'`. Handles
are instance-local and disappear on restart. An exact Python session is in
[the GPU experiment guide](../../experiments/gpu/README.md).

`make test-gpu` tests real launches through a forwarding test-only interposer,
unwrapped CPU/GPU results and complete state, bad proofs before compilation,
missing/substituted bundles, runtime rebuild/change, device/allocation/launch/
synchronization failures, unavailable devices and durable reopen. The test
interposer never supplies synthetic successful results and is absent from
production and benchmarks. `make benchmark-gpu` uses the heavy lock and
`paper/bench/fixed-clock.sh`; both targets reuse an inherited
`JAYDB_HEAVY_LOCK_FD` to avoid nested-lock deadlock.

The proof concerns the checked Book's semantics, with the same obligations
and checked Gate/finisher path for CPU and GPU; no CUDA validity axiom exists.
T2 now also trusts the official emitted runtime's CUDA path, NVRTC, CUDA driver,
managed memory and GPU hardware. Differential testing is evidence, not proof.
Host artifact checks assume protected tools/files and do not defeat a hostile
same-UID file-use race. The live worker receives the same configured GPU
option as ordinary execution.
See [raw measurements and limits](../../paper/evidence/gpu-programs.md).
