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
execution. The three logical limits measure canonical message, state and
response bytes. Equality with a ceiling is allowed. Execution has no
total-process memory budget or deadline.

## Checked migrations

Enable online migration with `--admin-socket PATH`. Connect to the owner-only
Unix socket and send one UTF-8 JSON line of up to 65,536 bytes including the newline.

```json
{"command":"migrate","configuration":"/path/new/Configuration.bend","migration":"/path/Migration.bend"}
```

The host closes the connection after one JSON response. On success it returns
`{"status":"success","lsn":42}` with the epoch's actual LSN. On rejection it
returns `{"status":"error","code":"data","message":"migration returned data"}`
with the actual error code and message. Client connections stay open across
the cutover. Prepare programs again because every old handle is retired. For
quiescing and durable recovery, see [Schema changes](../../docs/live-engine.md#5-schema-changes).

The host uses the same staging entry point available for standalone checks.

```sh
node --stack_size=65536 tools/service/stage.mjs migrate WORKDIR \
  OLD_CONFIG_OR_ENV NEW_CONFIG MIGRATION BEND_SOURCE BENDTT
```

Use a fresh private work directory and the pinned Bend source and bendtt paths.
Pass the active frozen environment directory as `OLD_CONFIG_OR_ENV` for a
published database. A configuration file is also accepted for standalone builds.
`NEW_CONFIG` is a configuration file. The JSON result gives the executable
`program`, the new `limits`, the frozen `newEnvironment` directory, and the
`programs` and `stagePath` used by the new environment.

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
task application's public helpers using `applications.tasks.app.prepare`.

## Call path

The [prepared-program extension](PREPARED_PROGRAMS.md) checks a universal
certificate at registration. The host starts workers for each handle on
demand and reuses workers from the instance-wide idle pool. Ordinary calls
still check and compile each concrete certificate and run a one-request worker.

The host loads the canonical initial state into an indexed snapshot. A checked
startup executable exports the configuration's schema, and the host checks
that the exported schema and state fit the store's representation. The
framing reader queues declarations and reads ahead within its byte budget.
Concrete admission and controls use checked `Dispatch.authentication` with
a projection containing the table layout and matching user, if any. Dispatch
checks and decodes the full envelope before authentication and admission.

The generated entry calls `Remote.packet` (ordinary) or
`Remote.registered_packet` (prepared). The prepared worker receives the
controller-issued entry for the requested live handle and the original
request body. It authenticates through the host's credential index before
resolving the handle, then checks the resolved source and proof against the
artifact's frozen bindings. The concrete
oracle also compares the context and structural arguments with its admitted
instance. Both workers ask for data operations over private framed pipes.
The host applies those operations to a transaction on the current snapshot.

A worker final frame contains a tag and the exact framed response. Tag 0 keeps
the current state. Tags 1 and 3 both propose success, so the host checks the
candidate state before choosing the final response. The store maintains row
structure on writes and checks credentials and canonical size at commit.
After successful validation, tag 1 can publish and tag 3 forwards the
worker's response-check error without publication. A malformed frame or
worker failure discards the transaction and returns `failure`. A later
prepared call reuses another idle worker or spawns one on demand.

Prepare/invalidate use the separately checked `Control.control` transition through
`ControlBridge.packet`, compiled at startup. The native controller checks the
current identity, full envelope, exact universal admission tuple, lifetime
freshness and bounded receipt before returning the registry delta. Rust stores
the returned registry bytes, manages admitted artifacts and copies receipts.
`ControlTheorem` and the mixed service fold cover those decisions; physical
artifact integrity/cleanup and external process failures remain host duties.

Each session completes execution, cleanup and publication, then writes and
flushes the response before selecting another request. Stdin/stdout is the
default single session. `--listen SOCKET` serves multiple FIFO sessions on a
Unix socket with the same frames. Socket threads read one message at a time
and leave later frames in the socket receive buffer. The host accepts up to
128 live client sessions and closes extra connections. The listener can
reclaim a stale socket pathname when a connection is refused. Non-socket
paths and active listeners are left alone.

A shared execution gate limits active transactions, and gives exclusive
operations priority over new shared attempts. Prepare compilation uses a
separate pool sized to the execution bound. Installation and invalidation run
exclusively. Installation rechecks the epoch, registry and authentication
view used by the controller. The committer revalidates write transactions against the latest
staged snapshot, in order. A conflict reruns the whole request from a fresh
snapshot. After three conflicts a request runs exclusively. Direct workers
are reaped before response readiness. The instance keeps at most one idle
prepared worker per execution slot and evicts the least recently used idle
worker when the pool exceeds that budget. Prepared workers are also retired on
invalidation, migration, worker failure or shutdown.

The stdin framing queue includes a body currently being read ahead. It holds
at most eight items and 1 MiB of speculative body bytes. A larger body waits
for dispatch before the reader fetches it. The coordinator accounts for one
selected request and its response. The current epoch's logical message limit
is applied at dispatch on both stdin and sockets. Allocation failures for
lengths inside that limit are technical transport failures. Snapshot and worker
memory are separate from these framing bounds.

Clean EOF drains complete requests. Partial header/body and oversize declarations
produce terminal input/limit responses after preceding complete frames. Input or
output I/O failure stops the affected session. In stdin mode a cancellation socket
wakes the framing reader so it can be joined before the service returns.

Compilation directories receive code, proofs, and public admission data, never
a full transaction snapshot. The seed participates only in initialization
and is removed before serving. Execution workers receive requests and
answers and send operations and final responses. A migration reads the full
state over its private pipe.

## Ownership and failures

The Rust host owns each process and its pipes. The live worker protocol
alternates request, operation and answer frames through finalization. Startup
and admission helpers still use concurrent input, output and stderr capture.

The Linux host supports stdin/stdout and local Unix sockets. Its default
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
lock. The committer appends one atomic write-set record per accepted write
transaction and synchronizes the batch once before publishing its final snapshot
and releasing the responses. Read-only successes use their already durable
snapshot and skip the WAL. When a batch crosses a 256-LSN boundary and the
queue has room, a background thread writes a checksummed checkpoint. Recovery
loads the newest valid checkpoint and replays later records in LSN order.
It can discard a damaged final batch. It rejects interior corruption, LSN
gaps and a damaged checkpoint whose LSN the retained log cannot reach. WAL
batch bodies use a 32-bit length field. An append or sync failure stops the
process. Users and application
tables, including any idempotency receipts, survive restart. Prepared handles
and their allocation history are instance-local.

Recovery requires the exact current durable environment, including actual
controller executable bytes. After migration, open with the migrated
configuration and preserve the controller executable and its sources/tooling.
Process death tests do not establish hardware power-loss safety.

With the old service stopped, run `./jaydb2 --configuration FILE --storage NEW_DIR --upgrade-from OLD_DIR --legacy-jaydb2 /path/to/main/target/release/jaydb2` for a one-way upgrade to a new directory.
Keep the original trusted executable and its source checkout available so the upgrader can verify the exact legacy environment, checksum, and limits on a private copy while leaving `OLD_DIR` untouched.
After the upgrader verifies that the canonical state loads under the current schema, open `NEW_DIR` normally with `--storage-mode open`.

The Node helper uses only a public stack-size option, without an addon or Bend
change. The stage uses Clang 19 with `--no-default-config`; native programs
receive the official `--threads N --gpu off` options by default. For CPU socket
sessions, `--concurrency N` accepts 1–128 and defaults to available CPU
parallelism capped at 128. With more than one execution slot, each Bend
process defaults to one runtime thread. With one slot, it defaults to the
same available CPU count. `--threads N` overrides the native thread budget
for all stages. The committer owns publication and each session owns its
response delivery.
Installation of these tools is part of the trusted environment.

Optional [administrator timing](SERVICE_TIMING.md) records monotonic elapsed
service time through cleanup and result readiness, before response delivery.
Each record includes the count of OCC `retries` and the `wal_batch` size
(zero unless a durable batch published the write). The inspection socket emits
complete metadata/state pairs, with the snapshot's `lsn` and a `request` ID
that links concurrent events and retries.

## Verification and remaining host obligations

The [remote refinement proofs](../../proof/README.md#live-worker-refinement)
connect representable data exchanges to `S.step` and lift the result to
finite certified prefixes. The generated `generated_oracle_sound` law
supplies the logical oracle premise. Reference worker and control proofs
remain part of the contract aggregate.

The [proof guide](../../proof/README.md#trusted-base) numbers the host's T3
duties. They include exact input and artifact binding, supplying the
controller-issued prepared entry, faithful store operations and validation,
FIFO sessions, OCC, atomic WAL-backed publication, recovery and migration
cutover. T1 supplies checker soundness and exact source/Book binding.
T2 supplies compiler and runtime preservation. The native loop effect,
Rust bridge and physical IO are trusted.

Error-code classification and response construction execute in the existing
checked native controller. Its private metadata is a canonical text value
containing the exact observed error code, distinct from the four-text prepare
metadata list. The remaining packet contains the latest registry, the empty
authentication projection and an empty body. `ControlBridge.run` calls
`Control.host_error`, which uses the table in `contract/HostErrors.bend`
and `Control.finish`'s denial.
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
memo remains valid for later roots under the same configuration. Migration
prefills the same exact-code replies for the new configuration. Prepared
map/integrity denials use these entries without another child. Other codes,
including `HOST_IO`, use their own entry or the checked controller.

Detection of handle misses and integrity failures, exact code forwarding
and the technical fallback remain host duties. A literal-code inventory test
checks the classification of codes found in the Node tools.

If the denial controller or its transport fails, Rust keeps the root and emits
the fixed technical fallback with an explicit stderr diagnostic. The fallback
is never memoized. Startup performs two checked denial computations.

Prepare/invalidate replies come from the controller under `ControlTheorem`,
with bounded receipts and checked registry changes. The Dispatch bridge
covers early dispatch denials. `ControlRegistryBytes` proves the reference
registry round trip. The live host must project the requested entry faithfully.

`make test` rebuilds before native/integration tests. `make verify-contract`
and `make verify` check the inhabited executable Init/Core/Ingress/UnifiedCore/
Fold, wire and reference worker theorems with both official tools.
`make verify` also checks the live remote refinement and causal negatives.
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
hashes before releasing a program path. Rust checks the artifact before
launching a worker. A checking, build or binding failure releases no worker. On every reported failure,
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
and publication are measured separately. With `--gpu`, checking precedes
building. The post-run CUDA checks fall inside `ordinary_worker` or
`prepared_worker`.

## Experimental GPU programs

Opt in on Linux/NVIDIA with `--gpu 512`: integer corpus MiB from 64 through
4096; the default remains `--gpu off`. Initialization, authentication and the
checked metadata controller always use CPU. CUDA uses one execution slot
per instance, including for read-only programs. The corpus setting does not change the three
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
each exchange and before accepting output. CUDA prepared execution checks the
sealed bytes before and after each exchange. CPU prepared artifacts are
validated at spawn.
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

CPU and GPU use the same checked live worker and satisfy the same laws.
T2 now also trusts the official emitted runtime's CUDA path, NVRTC, CUDA driver,
managed memory and GPU hardware. Differential testing is evidence, not proof.
Host artifact checks assume protected tools/files and do not defeat a hostile
same-UID file-use race.
See [thesis measurements and limits](../../paper/evidence/gpu-programs.md).
