# Repeated prepared calls: measurement and design

Research only, 2026-11-12. No engine, theorem, admission, compiler, emitted C or
runtime source changes. Baseline source commit:
`3f28eb7c69d5da06b2bfe89ce3d720ed6d581acc`. Measurements use the pinned Bend
2.0.39 and both official checkers. Raw observations, fingerprints and commands
are in `perf-repeated-diagnosis.json` beside this report. This is a one-machine
latency diagnosis, not a PostgreSQL comparison experiment.

## Scope and method

The machine is an Intel i7-11700K, 16 logical CPUs, Linux x86-64, Clang 19.1.1,
Node 24 and a release Rust host. All builds, experiments, profilers and benchmarks
hold `/tmp/jaydb2-experiments-heavy.lock`. All final timing observations run
inside `paper/bench/fixed-clock.sh` (performance governor, turbo disabled).
Other experiment threads use that same lock. The harness does not pin a core;
these are warm page-cache observations, not cold-disk measurements.

The service experiment uses the existing point-program fixture, two users,
10 or 1,105 two-column rows, no administrator inspector and volatile storage.
The requested read targets the **last** key. Updates alternate its integer
between 0 and 1. Each condition has one discarded warmup and 100 measured calls
in one service session. The host's opt-in phase markers and timing log are on;
no preload observer or syscall profiler is on in those service samples.
This is not a durability/fsync experiment. Initialization and preparation are
outside the call intervals.

A separate replay harness includes production `server/capture.rs` unchanged,
so it uses exactly the host's three scoped pipe threads and `Command::spawn`.
It executes copies of the admitted artifacts and reconstructed canonical
private packets. Replay checks the full returned packet is stable and verifies
success values; the input registry includes the actual live handle, frozen
identity, source/proof and preparation history. Copying admitted bytes does not
recheck them or create a new admission claim. The saved native receipt records
`primary: true`, `bendtt: true`, universal certification and exact C/source
hashes. See the limitations below about separate timing runs.

`perf` and `strace` are installed; `ltrace` is absent. Unprivileged `perf stat`
fails at `kernel.perf_event_paranoid=4`; `sudo -n perf stat/record` works.
Root BPF uprobes time existing symbols in the unmodified `-O2` executable.
No generated C is patched, and no runtime is replaced for instrumentation.

## End-to-end measured costs

| Inclusive phase, median ms | Read / 10 | Update / 10 | Read / 1,105 | Update / 1,105 |
|---|---:|---:|---:|---:|
| Authenticator process + hash/transport | 1.263 | 1.273 | 10.059 | 10.191 |
| All sealed-file rereads/comparisons | 0.630 | 0.627 | 0.940 | 0.951 |
| Prepared worker + hash/transport | 1.945 | 1.952 | 26.021 | 26.685 |
| Publication | 0.000 | 0.000 | 0.005 | 0.006 |
| **Complete client round trip** | **3.894** | **3.915** | **37.078** | **37.938** |
| Round-trip p95 | 4.026 | 4.040 | 37.608 | 40.130 |

`packet_authentication` includes input packet construction, authenticator
executable validation, transport/thread/process setup and the checked pass.
`prepared_worker` includes its executable validation, registry packet creation,
transport, complete native execution, output collection and child reaping.
`prepared_integrity` includes parsing authenticator metadata/map lookup and
rereads the entire sealed file set, including literal C,
proof/source files, manifests and the executable. These phase rows are inclusive;
**do not add their nested profiler measurements again**. Medians of separate
phases need not sum to the median complete call.

Native worker medians from 30 post-warmup BPF observations per condition, ms.

| Instrumented region | Read / 10 | Update / 10 | Read / 1,105 | Update / 1,105 |
|---|---:|---:|---:|---:|
| Runtime main → stdin effect | 0.1275 | 0.1263 | 0.1399 | 0.1414 |
| C input read + native byte-list construction | 0.0314 | 0.0306 | 0.9064 | 0.8809 |
| Checked entry: packet/registry/root/body/authentication | 0.8339 | 0.8335 | 8.6420 | 8.6380 |
| ↳ Generic root codec + fixed limit conversion | 0.2310 | 0.2327 | 2.4199 | 2.4204 |
| ↳ Generic value → typed state | 0.0072 | 0.0072 | 0.2512 | 0.2493 |
| ↳ Authentication, resolution and oracle (inclusive) | 0.1549 | 0.1545 | 0.1548 | 0.1558 |
| Actual checked access/interpreter step | 0.0068 | 0.0119 | 0.3102 | 0.7626 |
| Stopped transition | 0.0008 | 0.0008 | 0.0009 | 0.0010 |
| Finalization and canonical output construction | 0.1908 | 0.1911 | 14.2970 | 14.4009 |
| ↳ Final structural work before first state encoding | 0.0196 | 0.0195 | 1.3928 | 1.3942 |
| ↳ First state encoding/size check + response preparation | 0.1013 | 0.1019 | 7.0688 | 7.1683 |
| ↳ Second state encoding and Commit joining | 0.0696 | 0.0696 | 5.8152 | 5.8528 |
| C native byte-list → output buffer | 0.0062 | 0.0062 | 0.3789 | 0.3831 |

Root structural validation to `Dispatch.received` adds 0.0207, 0.0207, 1.3953, 1.3934 ms in the same column order. The full root-decode region is 0.2589, 0.2610, 4.0687, 4.0664 ms; the rest of entry includes nested packet cuts, registry decoding, octet scans, request bounds/decoding and disposal. Nested rows overlap their parent. Small probes affect these microsecond-scale measurements.

| Separate authenticator, instrumented region | 10 rows, ms | 1,105 rows, ms |
|---|---:|---:|
| C input/list construction | 0.0105 | 0.8723 |
| Complete checked decode/authentication/metadata and state disposal | 0.4955 | 8.1123 |

| Isolated instrumented fresh credential check | 10 rows, µs | 1,105 rows, µs |
|---|---:|---:|
| Authenticator `Data.authenticate` → Input continuation | 3.59 | 3.76 |
| Worker Gate `Data.authenticate` → Gate continuation | 2.82 | 2.99 |

These boundaries were selected from the actual generated continuation code, not arbitrary C function returns. They include current-registry matching/context construction and its state-reference disposal; the worker row measures Gate authentication (the additional Resolve authentication is not separately isolated). The ~0.155 ms wider worker region above also includes live lookup, artifact/oracle string matching and setup. The authenticator’s larger region includes generated instance/links and retiring the full decoded state. Probe overhead is material at a few microseconds; these are diagnostic durations, not uninstrumented credential-only CPU estimates.

The 8.642 ms worker entry at 1,105 rows includes 4.069 ms decoding/converting/validating the root itself. Only about 0.310 ms is the point access. Finalization/output construction is 14.297 ms, including two state encodings; these are independently consistent with the no-serialization counterfactual below.

Process/host subcosts measured independently:

| Component | Result |
|---|---|
| Same-path dynamic hello, 300 samples | **0.3520 ms** complete capture/reaping; not just a fork syscall |
| Three host pipe-thread `clone3` calls | About 20–31 µs each under strace; six threads across two native processes per call |
| `posix_spawn` kernel path | `clone3(CLONE_VM|CLONE_VFORK|CLONE_CLEAR_SIGHAND)`; about 0.176–0.188 ms traced parent span, including child exec work |
| ELF `execve` | 0.108–0.119 ms in the large traced child; overlaps the parent spawn span |
| ELF loader itself (`LD_DEBUG=statistics`, n=3) | Worker 66,874 TSC cycles ≈ 18.58 µs; not the whole exec-to-main interval |
| Sched-exec event → C main | 0.193 ms / 0.221 ms for small/large worker; includes remaining kernel transition, loader, CRT/constructors, faults, scheduling and probe cost |
| CPU corpus/stack reservation | One 8 GiB and one 2 GiB `MAP_NORESERVE` mapping; 7–8 µs each in the large trace |
| Worker ready before stdin | 2,456 KiB RSS, 116 minor faults; ~10 GiB virtual size. After large request: 989 total minor faults, 0 major (one diagnostic process, stdout `/dev/null`) |
| Authenticator ready before stdin | 2,312 KiB RSS, 107 minor faults; after large request 807 total minor faults, 0 major, same diagnostic |
| Worker executable file read / in-memory SHA-256 | 0.0183 / 0.2293 ms; combined 0.2479 ms (359,040 bytes) |
| Authenticator executable read / in-memory SHA-256 | 0.0099 / 0.1351 ms; combined 0.1451 ms (211,480 bytes) |
| Sealed set | 128 files / 1,847,862 bytes, including 757,521 bytes of literal worker C; measured inclusive host phase 0.630–0.951 ms |
| Pipe transport floor beyond empty echo | About 0.017 ms for 65,536 echoed bytes, 0.095 ms for 262,144; input and output combined, separate 200-sample conditions |

These components are **not additive**: spawn/exec intervals overlap; strace slows syscalls; BPF includes probe work; loader cycles exclude other startup. The syscall-entry BPF timestamp could not be correlated and was discarded (its raw first startup field is invalid); only the valid sched-exec/main interval is summarized. Precise user-space vs kernel loader/fault attribution is not claimed.

| `perf stat`, execution plumbing + child, per run | Auth / 10 | Worker / 10 | Auth / 1,105 | Worker / 1,105 |
|---|---:|---:|---:|---:|
| Task-clock ms | 1.167 | 1.752 | 9.894 | 25.814 |
| Cycles, millions | 4.114 | 6.217 | 35.461 | 92.697 |
| Instructions, millions | 8.277 | 14.427 | 109.234 | 272.401 |
| Minor / major faults | 250 / 0 | 275 / 0 | 812 / 0 | 994 / 0 |

These counters include the replay harness, its three pipe threads, descendants and its output digest outside the timed capture; 31 executions including warmup. The separately observed native-only memory probes above distinguish initial faults from request allocation. No per-fault CPU-time attribution was measured.

## What actually executes

`tools/service/stage.mjs` generates a closed `main` which does
`Native.read()` followed by `launch(entry(bytes))`. A prepared entry is
`Worker.registered_packet(Transport.separate(bytes), code, proof, admit)`.
The exact admitted Book goes to official `compile_book`; `compile.mjs` builds
its literal C with `clang-19 -std=gnu11 -O2 -w --no-default-config ... -lm
-pthread`. Ordinary one-off workers use `-O0`; reusable workers and the
initializer/authenticator use `-O2`. The C embeds the JayDB foreign effects
through the supported `io_eff` mechanism; it does not load `effects.c` at run
time.

The C `main` parses runtime options, calls `corpus_setup`, enters `io_loop`,
then `io_sync`. `corpus_setup` reserves an initial 8 GiB CPU corpus with
`MAP_PRIVATE|MAP_ANON|MAP_NORESERVE`, sets allocator banks and copies the static
image. `io_loop` reserves a 2 GiB evaluation stack plus guard and signal stack,
installs signal handlers and creates an internal wake pipe. These are virtual
reservations, **not** 10 GiB resident allocations. Touches and minor faults,
not zeroing the entire reservation, account for physical memory work.

`native/effects.c:jaydb_read` reads until EOF using a 64 KiB initial malloc
buffer, then official `io_list` creates one native list cell per octet. Thus
leaving stdin open prevents the current entry from processing a request.
`jaydb_output` uses official `io_cbuf` to consume a byte list into a growing C
buffer, then `io_out`/stdio writes stdout. `jaydb_loop_run` repeatedly evaluates
the closed checked `step` using `corpus_eval`, transferring the linear captured
state, until `FinishOutput`. No state is loaded from the artifact directory.

The complete native runtime control vocabulary in pinned
`.tools/bend-source-2.0.39/bend2/comp.ts` is:

| Option/control | Meaning |
|---|---|
| `+RTS ... -RTS` | Delimit runtime options from application arguments. |
| `--RTS` | Treat the remaining arguments as application arguments. |
| `BENDRTS` | Whitespace-separated runtime defaults, parsed before command-line options. The host sets it to empty. |
| `--threads N` | Positive integer; pool clamps to 1–128 (help advertises that range; the Rust host enforces it). Runtime default derives from online CPUs, affinity and cgroup CPU quota. |
| `--gpu on`, `--gpu off`, `--gpu SIZE` | GPU policy; SIZE accepts numeric `MB`/`GB`, at least 16 KiB. Default probes GPU only when the Book contains GPU bangs. |
| `--gpu-build` | Build/write GPU program and exit; unsuitable for execution. |
| `--help` | Print help and exit; unsuitable for execution. |

There is no CPU heap-size, stack-size, GC, memory-prefault or Unix fork-server
runtime flag. CPU thread creation is lazy in `pool_open`, not unconditional in
`main`. IO helper pthreads are also lazy, for asynchronous official IO work.
`IO.spawn` and `IO.fork` in Base create IO computations/channels, **not Unix
processes**. The host itself creates three pipe pthreads per native run,
including authentication: six per successful prepared call.

## Feasibility and trust impact

### (a) Immutable admitted executables: feasible; change the integrity contract explicitly

`Program::run` rereads and SHA-256 hashes its executable on **every** run.
Prepared execution additionally calls `PreparedProgram::validate`, which
lstats/rereads every captured file and compares exact bytes. Replacing these
with an mtime/size/inode cache is unsound: same-size changes and write/exec
races remain possible. Keeping a read-only ordinary fd does not make its inode
immutable either. Current reread-then-path-exec also has a check/use window;
its correctness already assumes host-owned artifact storage is not maliciously
changed between those operations.

The sound candidate is an owned executable fd created at admission/load:
copy the released ELF bytes, verify them against the admitted receipt, add
`F_SEAL_WRITE|F_SEAL_GROW|F_SEAL_SHRINK|F_SEAL_SEAL`, verify `F_GET_SEALS`, and
execute that exact fd. Keep it alive with RAII; fail before execution if load,
sealing or fd identity checks fail. Hash the sealed image, not merely an earlier
path snapshot. Use `fexecve`/`execveat(AT_EMPTY_PATH)` or a carefully retained
`/proc/self/fd/N` path. CLOEXEC is appropriate for this ELF; script interpreter
fd semantics are different and irrelevant here. Do not use a writable mapping
as an immutable image; `F_SEAL_WRITE` must actually succeed. An fd-exec
`pre_exec` callback can disable Rust's `posix_spawn` fast path; use only
async-signal-safe child operations and benchmark that launch path. The tested
`/proc/self/fd/N` alternative retains ordinary `Command::spawn` behavior.

The prototype verified `F_GET_SEALS == 15`; write, growth, truncation and
further `F_ADD_SEALS` attempts each failed with `EPERM`. Actual
`os.execve(fd, ...)` succeeded and returned the exact original checked packet,
with cwd `/tmp`. The ordinary Rust spawn path through `/proc/self/fd/N` also
returned identical packets for both state sizes. Its medians were 1.634 ms at
10 rows and 25.548 ms at 1,105; ordinary un-hashed capture was 1.625 and
25.645 ms. Native execution is effectively unchanged: the saving comes from
removing repeated checks, not from a faster checked program.

The ELF is **dynamically linked** to `ld-linux-x86-64.so.2`, `libc.so.6` and
`libm.so.6`; the loader also consults `/etc/ld.so.cache` and `/etc/ld.so.preload`.
Runtime CPU discovery reads cgroup/sysfs information even when `--threads` is
explicit. Dynamic linker inputs and inherited `LD_PRELOAD`/`LD_LIBRARY_PATH`
remain outside executable seals. The current per-call executable hash and
sealed-source check do not protect those either. State and request are pipes;
no staged `.bend`, manifest, C or runtime-directory file is consumed by this
already compiled worker. The trace inventory below distinguishes dependency
reads from hardware-policy reads.

T1 must still bind both checker acceptances, exact Book/C, native receipt and
sealed ELF. T2 still trusts compiler, linked runtime/libc/libm, loader, kernel
and approved execution environment. T3 changes from per-call path rereads to
verified immutable-fd ownership, seal checking and fd-based execution. Kernel
seals become an explicit enforcement dependency; this is not a new proof that
arbitrary host code is sound. Static linking literal emitted C can eliminate
the separate dynamic ELF dependencies, subject to a new manifest/compiler-flag
policy and the same T2 preservation assumption.

`proof/README.md` duty 7 explicitly requires exact physical artifact checks,
and `native/SIMPLE_RUNTIME.md` says hash before every call. Those descriptions
and artifact-tamper tests must be revised deliberately if authoritative storage
becomes immutable fds. Calling changed on-disk source trees “irrelevant” cannot
silently satisfy the old fail-on-mutation behavior. If that exact behavior must
remain for *diagnostic copies*, keep their checks and lose that part of the
saving. Better: make an immutable admitted bundle authoritative and treat
mutable staging as disposable. Shared public/runtime files are still read for
**future** preparations: freeze those inputs in memory/immutable storage, or
revalidate when compiling. Never extend a worker-only optimization into an
unchecked future-admission shortcut. Both-checker admission and negative proof
rejections remain mandatory.

### (b) One authoritative authentication in the prepared worker: feasible with ABI/proof work

The extra process has no authority needed to authorize the existing prepared
worker. `Worker.root` decodes the current complete root, `Dispatch.received`
checks the original body and opcode-inclusive bound, `Resolve.select`
authenticates against that root, requires an empty raw proof and resolves the
live scoped registry entry; the artifact guard binds its code/proof. The
selected request then reaches `Gate.begin`, which authenticates again before
calling the checked sound oracle. This is fresh authentication, not a cached
principal. Credential authentication here is current-registry string matching;
it is not a per-row cryptographic computation. The control registry must still be the latest controller bytes.

The host uses authenticator output for four things:

1. Its leading tag chooses direct execution (1), preparation (3), prepared
   execution (4) or invalidation (5).
2. The principal frame sets `attempt.authenticated(principal)` for administrator
   timing. It must be the exact checked context ID, including a valid empty ID.
3. For tag 4, `code` is the handle used to locate the artifact. The checked
   registry and worker guard, rather than that map, authorize execution.
4. Tag 0 supplies an already framed early Keep response for body decode/limit,
   authentication or empty-proof validation failures. Direct/prepare success
   metadata also supplies code, proof, generated instance and dependency links;
   prepared execution discards the generated instance/links.

`proof/DispatchBridge.bend:dispatch_denials_equal_ingress_unified_early` already
proves tag-0 response equality to the corresponding checked early composition.
`WorkerBridge.prepared_packet_equals_real_registry_selection`,
`CertifiedWorker.checked_prepared`/`artifact_checked`, `UnifiedCoreTheorem` and
the service/control fold establish selection, current-root authentication,
source binding and live-registry obligations. They do **not** demand two OS
processes. T3 duty 3 currently specifies admission after checked dispatch;
change it so tentative artifact routing is explicitly separate from authoritative
worker selection. Keep ordinary admission and controls on their current path.
The existing denial bridge is an implication for tag 0, not a total proof of
whole-host equivalence: tag 2 (private transport/metadata-generation failure),
process failures and timing observations need their own treatment. In particular
`Generate.instance` can return `None` after argument encoding/length conversion;
a total fast-path correspondence should prove that cannot occur for the accepted
bounded canonical requests in scope, rather than assume every old result was
a client denial.

A practical fast route recognizes only the exact prepared-execute envelope and
extracts a candidate handle with a bounded, total host parser. Pass the **whole
original body**, current root and latest registry unchanged. On any uncertainty,
missing artifact, control/direct opcode or malformed candidate, use the old
path. Never return a new host-generated input/authentication status based on
this parse. For candidate-hit cases the checked worker produces the denial or
executes the exact registered program itself.

“Untrusted parse” needs qualification: it is untrusted for identity and law
safety because a wrong artifact cannot bypass the checked guard. It remains
trusted for routing completeness, exact success/error behavior and progress:
a wrong candidate that reaches another sound artifact may return a technical
failure instead of the correct success. Either prove the host parser's routing
relation, or check a worker-returned route identity and retry/fallback **before
publication**, with a precise policy for failures. Do not claim that the
artifact guard alone proves observational equivalence of arbitrary routing.

A 15-case native matrix checked empty/malformed envelopes, invalid opcode,
truncated extension, invalid value, actual over-limit input, valid execution,
empty/bad credentials, nonempty proof, bad credential + proof, unknown/malformed
handles, invalid arguments and invalidation. **All ten tag-0 authenticator
results exactly equaled worker Keep bytes.** Unknown/malformed handles reached
worker `failure`; invalid arguments reached `refusal`; valid execution returned
the exact original root and value. Invalidation produced authenticator tag 5
and worker `input`: it must use the control fallback. This finite matrix is
regression evidence, not a proof of every routing case. Full read/update root
bytes were also decoded and compared with the expected state at both sizes.

The current worker ABI is only `Commit(root,response)` or `Keep(response)`;
it does **not** return a principal. Preserve logging by adding a checked result
projection/envelope with `Maybe<Context.id>` tied to the same fresh context.
Cover success, refusal, checked limits/data failures and authenticated missing
handles; match the authenticator's current validation order. `Dispatch.validated`
turns nonempty prepared proof into rejection before emitting principal metadata,
so today's logging is subtler than “every successful credential gets a name.”
Extend the two `Messages` principal laws and actual worker/ABI bridge, keep
`WorkerDecision`'s exact root/response projection, and update timing/observer
integration tests. An end-of-worker principal also cannot preserve today's
principal after an authenticated worker crash. Options are a separate checked
early metadata message (new trusted IO framing/order), an explicitly documented
null-on-technical-failure policy, or retaining the old pass when the timing sink
requires that behavior. Do not silently weaken `SERVICE_TIMING.md`.

An alternative if two-stage logging/failure behavior must remain is a **checked
user-registry projection** cached with each published root. `D.authenticate`
ignores application tables. Have initialization/recovery and every checked
Commit carry exact encoded user rows, prove their projection/authentication
relation to the paired full root, and atomically retain/forward that pair in
T3. A specialized authenticator could then decode just users plus the original
body while preserving the existing principal-before-worker boundary. This was
not prototyped: it should remove most of the row-dependent authentication work,
but keeps a process floor and adds a projection ABI, startup/recovery and cache
coherence proof/host duty. Do not extract or refresh it through an unchecked
Rust state parser, and test user deletion, credential rotation and recovery.

### (c) Persistent workers versus pre-executed single-use workers

The current executable cannot handle two requests: `Native.read` consumes EOF,
`launch` writes one decision, and C `main` exits. Sending two frames simply
makes one malformed body. There is no supported `+RTS` server/fork option and
no external way to fork a process *after* it has initialized Bend without a
forking program, injected code or checkpoint mechanism. A normal external
fork-server which execs the worker still pays Bend initialization. A JayDB-owned
foreign effect could make the native program itself a Unix fork-server, using
the supported compiler foreign mechanism; it would add trusted fork, allocator
and thread-safety duties. It is not an existing Bend/runtime feature and was
not prototyped here.

It is nevertheless possible to build a long-lived server **without changing
the compiler or literal-emission rule**: JayDB owns the trusted foreign effects
and generated Bend wrapper. Base supports `IO.bind`, files with binary reads
and writes, channels and finite IO loops (for example `App.loop` with fuel).
A framed trusted read/serve effect and a checked finite multi-request wrapper,
or a trusted IO driver calling the fixed checked entry, can repeat requests.
An indefinite service loop can remain a documented trusted driver effect, as
today's native stepping loop already is. This is an extension of JayDB's own
ABI/effects; it is not a runtime flag. Arbitrary submitted programs must remain
pure and terminating, with no new access to those effects.

A true persistent worker changes the contract's fresh-private-process premise,
cleanup-before-publication and failure isolation. Prove each request's checked
entry/finalization and a serial state/registry/response fold; document framing,
reset, ownership, cancellation and crash behavior in T2/T3. Retaining decoded
state needs authoritative versioning/acknowledgment across other prepared
programs and user-registry changes. Otherwise only spawn/init are removed and
state is still decoded on every request. Official compiled functions are fixed
in the Book; hot-loading arbitrary new prepared code as a DSO is not supported
by the current ABI. A closed compiled catalog is another possibility, but adding a
registration would then require checking/compiling a new catalog generation and
a checked state/registry handoff; checker fuel and Book size are real constraints.
A per-artifact persistent process cannot magically retain
the current full database when another artifact commits.

The lower-risk alternative is a pool of **single-use** admitted processes,
already exec'd and blocked in stdin read. Supply no state, credentials or live
registry until actual FIFO request selection. Close stdin to deliver EOF;
collect and reap exactly as today. Spawn replacements ahead of future calls;
kill/reap unused children on invalidation/shutdown. Ownership of handles and
which process receives which root remains T3; all existing checked request
paths and fresh-process isolation can remain intact.

| Rows / operation | Process | Spawned capture, ms | Already waiting, ms | Hidden latency, ms |
|---|---|---:|---:|---:|
| 10 / read | auth | 1.053 | 0.603 | 0.451 |
| 10 / read | worker | 1.625 | 1.167 | 0.458 |
| 10 / update | worker | 1.635 | 1.174 | 0.460 |
| 1,105 / read | auth | 9.913 | 9.325 | 0.588 |
| 1,105 / read | worker | 25.645 | 25.118 | 0.527 |
| 1,105 / update | worker | 26.229 | 25.624 | 0.604 |

The pool numbers measure request delivery through complete output/reaping,
with process/thread creation and readiness waiting outside that interval.
Readiness was verified through `/proc/PID/wchan` showing a pipe read, not a
fixed sleep inside the timed interval. It is a latency-hiding prototype, **not**
a measured throughput improvement. Refill consumes CPU; deeper idle pools
consume descriptors and memory. After removing separate authentication, only
the worker's pool saving remains; do not also credit the removed authenticator.

### (d) Whole-state work: the principal scaling problem

The measured two-point read slope is **30.31 µs/row**, update **31.07 µs/row**.
A 1,105-row read spends approximately 0.91 ms on C input/list building, 8.64 ms
in checked entry/selection, 0.31 ms in the actual access, 14.30 ms in
finalization/encoding, and 0.38 ms converting output to a C buffer. The separate
authenticator repeats input/list building and an 8.11 ms checked pass. This
fixture's state/row work dominates spawn and pipes.

As a control using the same admitted worker, bad credentials take **11.010 ms**
and refusal without a read takes **11.031 ms** at 1,105 rows (no hashes/sealed
rereads). Both still receive and decode the full snapshot; neither serializes a
successful root. At 10 rows they take 1.347 and 1.450 ms. This independently
supports the approximately 14–15 ms success-finalization/output budget. These
are different request outcomes, not optimized successful-read benchmarks.

The wire representation is verbose: each two-column row is 59 bytes, repeating
record framing, `id` and `value` field names, text and integer tags. State bytes
are 898 at 10 rows and 65,503 at 1,105 rows (see raw fixture metadata for the
authoritative sizes). That byte list is built in C, scanned for octets by
`Transport.separate`, cut/reversed into blocks, measured again by Codec,
decoded byte by byte into `D.Value`, converted into `D.State` and structurally
validated. Prepared transport has an extra registry frame and octet scan.
This is much more work than the pipe copying itself. The one live registration
also sends 2,592–2,665 bytes of registry/source/proof/history per call; these
measurements do not characterize scaling with many live prepared registrations.

Success, including a read, enters `Requirements.finalize`. It checks full state
structure and calls `fits(limit_state, D.state_value(w))`, which constructs a
full canonical encoding and measures its length. Later
`Execution.encode_decision` again calls `Protocol.encode(D.state_value(state))`
for Commit output. A read therefore decodes state twice across the two
processes and encodes state twice inside the worker. The theorem intentionally
permits equal-root **Commit** on success; changing it to Keep merely because
no row changed would violate `WorkerDecision.keep_iff_non_success` and host
publication/last-response semantics.

Ordered source-level opportunities, all requiring both checkers:

* **Reuse the finalizer's canonical root bytes.** Return a checked package
  containing finalized status, exact published root/response and its encoding;
  transport that package to the existing Commit ABI. Prove the optimized path
  equals current `Requirements.finalize`/`Gate.finish`/`Execution` composition,
  including response and state limits and failures. Keep `WorkerDecision`,
  `WorkerBridge`, `CertifiedWorker` and Core completion/progress conclusions.
  This avoids one full encode without changing public wire or trusted duties.
  Alternatively a proved allocation-free encoded-size computation can replace
  the first encoding, but it must match `Protocol.encode`'s validity, overflow,
  Unicode, name-order and length failures exactly.
* **Make checked transport single-pass.** Fuse octet validation/cutting and
  avoid copying/reversing complete state lists at nested frame boundaries.
  Establish extensional equality to `Transport.separate`; update the framing,
  packet/registry bridge and causal malformed-packet proofs. Pure Bend changes
  can do this without trusting a Rust state decoder. Profiling determines the
  available budget below; this is not a promised universal speedup.
* **Specialize private decode before changing bytes.** A schema-driven Bend
  decoder can build `D.State` directly from the existing canonical private
  encoding, avoiding the intermediate generic `D.Value` and repeated scans.
  Prove equality on `Protocol.encode(D.state_value(s))` for valid states and
  the actual frozen schema. The existing T3 obligation already supplies those
  exact current-root bytes; document that provenance premise if the fast decoder
  relies on it. Keep the full public request decoder and its negatives intact,
  and specify malformed private-transport behavior explicitly. This may avoid
  a wire/storage migration, but still requires meaningful refinement proofs.
* **A schema-driven private codec.** Encode a row as schema-ordered key/values,
  omitting repeated field names and tags known from the frozen schema. This
  fixture could use roughly 23–25 bytes/row rather than 59 (about 58–61% fewer
  row bytes), before table/user framing. That is a size estimate, not a
  measured latency speedup. Prove typed-state decode/encode inverses,
  canonicality, key ordering, schema/UTF-8/integer validation and the exact
  worker/persistence bridge. Keep the public value codec unchanged if
  possible. The public contract's state-size limit still measures the specified
  canonical state image; a shorter private encoding must not admit a state
  exceeding that limit. Existing `Codec*.bend` proofs are substantial and do
  not automatically apply to a new private representation.
* **Proved read-only/equal-root reuse.** Track a checked “state unchanged”
  invariant or admit a read-only effect certificate, then emit a new private
  `CommitReuse(response)` variant. Prove its logical next root equals the
  current root and still publish the new paired response. Use starting-root
  validity/size to avoid unnecessary final state encoding/validation. The
  `Entry.read_only` field currently stores `False` and is not such a proof.
  Update native decision/host publication/persistence bridges and test a
  no-op write, actual write, refusal, user mutation and limits. This can remove
  most success serialization on reads; it is not a general update optimization.

Partial state is a larger architecture change. A program may compute keys from
arguments or prior reads, enumerate/count rows, and branch on user data; code
text does not generally identify a complete fixed footprint. Supplying only
one row and interpreting the rest as absent gives a different database even
if that smaller root is structurally valid. Full-state law certificates do not
establish such a projection is equivalent. The initial state, fresh user
registry and all dependencies must remain bound to the actual published root.

Two concrete routes are (1) certified footprints plus a frame theorem proving
all observations/writes/global checks agree with the full root, or (2) a checked
root commitment/tree representation, membership **and absence**, count/order
witnesses, checked updates and a refinement proof to logical `D.State`/traces.
A host row cache alone is insufficient. Cryptographic commitments introduce an
explicit hash/collision-resistance assumption unless identity is checked in
another way; a host-selected subset adds a new T3 selection obligation unless
checked witnesses enforce it. Writes also need full credential uniqueness and
canonical state-size/finalization conditions, not just local row validity.
Expect high proof/architecture effort. The current list-based `find_row` and
`substitute_column` remain linear; replacing them with a proved map/index only
helps the much smaller body portion until transfer/encoding is fixed.

### (e) Other measured factors

A distinct small-state cost is JayDB's **unary Nat-to-u64 conversion**, not a
Bend runtime limitation. `contract/Bytes.bend:nat64` recursively decrements `n`
and increments two U32 words. `Dispatch.read_root` and `Input.read_message`
recompute it for fixed 65,536-byte limits. In the small read's sampled CPU,
`WL_FID_Bytes_nat64` and its continuation account for **19.13%** (5.91% +
13.22%). This explains part of the fixed decode cost even for tiny inputs.
Generate canonical frozen `Number64` limit literals with a checked equality
witness in the admitted Book, or add a proved logarithmic conversion and
rewrite hot uses through its equivalence lemma. Preserve overflow above u64
and the existing `nat64` reference laws; do not truncate through an unchecked
host conversion or change native Nat representation. The profile suggests an
approximately 0.15–0.30 ms per-worker budget at small state, **not a measured
optimized saving**. Generic conversion/proof work is greater than constant
specialization; both are JayDB source changes with no necessary new trusted
computation.

| Literal-C/host diagnostic | 10-row read, ms | 1,105-row read, ms | Interpretation |
|---|---:|---:|---|
| Original `-O2`, thread count 1 | 1.625 | 25.645 | Un-hashed production capture implementation |
| Original `-O2`, thread count 16 | 1.639 | 25.614 | No useful change; syscall traces show **zero Bend pthread clones** in these workers/authenticators, including at 16 |
| Literal same C, `-O3` | 1.640 | 25.566 | No meaningful demonstrated win; executable grows to 371,264 bytes |
| Literal same C, `-O2 -static` | 1.448 | 25.346 | Modest startup gain; executable grows to 1,383,440 bytes |
| Already waiting worker, 4 KiB pipes | — | 25.322 | Slower than 64 KiB pipes |
| Already waiting worker, 64 KiB pipes | — | 25.082 | Default fresh pipes observed here are already 64 KiB; no big buffer win |

Static hello capture was 0.250 ms versus dynamic hello 0.352 ms. **Static worker
read-plus-SHA-256 is 0.962 ms**, versus 0.248 ms for the original image: keeping
per-call hashing would more than erase the small startup gain. Consider static
linking only after immutable-image ownership. `compile.mjs` currently whitelists
`-O0/-O2`; the `-O3` and static binaries are scratch builds of exactly the
admitted C, not production policy changes. Both returned byte-identical read
packets at both sizes. No `-ffast-math`, LTO, target-specific flags, modified
runtime constants or custom representations were tested/recommended as a proved
optimization.

The large read's sampled CPU is 22.28% `term_drop`, 9.51% `span_fade`, 8.50%
`rfc_wrap` (40.29% together), 24.75% in byte concatenation/its continuation,
3.91% in byte-list length, 3.88% in transport cut and 3.02% in octet validation.
The authenticator similarly spends 29.42% in `term_drop` and 10.40% in transport
cut. These self samples identify list construction/disposal and repeated scans;
they cannot be added to separately measured inclusive regions. Reducing
intermediate objects/passes in JayDB source addresses this work without editing
the runtime's reclamation functions.

Normal prepared calls do not spawn Node or run either checker; Node checking
and Clang compilation are registration costs. The host's inspector is off in
these samples. Its normal prepared path does not JSON-decode the database or
inspect client results to determine success; checked Bend selects Commit/Keep.
The optional NDJSON timing and benchmark markers do add small host overhead;
remaining host work includes scheduling, vector copies, packet construction,
result framing, allocation, response logging and delivery. Source-level
inspector/JSON optimization cannot explain the 30 microseconds/row slope here.

## Recommended implementation sequence

The first two steps address the largest avoidable costs while retaining a full
snapshot and the checked gate. The following are incremental budgets **after
previous applicable steps**, with implementation effort/risk judgments rather
than delivery commitments.

| Order | Change / effort and risk | Estimated incremental saving | Trusted-base / proof consequence |
|---|---|---|---|
| 1 | Own verified immutable admitted images/bundles; moderate host work, Linux-specific | About **1.0 ms at 10 rows / 1.3 ms at 1,105** if both executable hashes and the whole sealed scan disappear | T1 exact admission-to-image binding; T3 fd/seal ownership and future-compilation input freezing; explicitly revise artifact-mutation policy. Keeping old diagnostic-path checks forfeits their 0.63–0.95 ms. |
| 2 | Prepared candidate routing + authoritative worker auth + checked principal result; moderate ABI/proof/observer work | About **1.1 / 9.9 ms**, excluding the auth hash already removed in step 1 | Current worker Core/Unified selection remains authoritative. New routing-completeness obligation and checked principal projection; explicitly resolve crash-time logging. Missing/doubtful/control cases fall back. A checked users projection is the alternative if the old separate-stage behavior must stay. |
| 3 | Freeze checked limit words / prove fast `nat64`; low-to-moderate proof work, checker-fuel risk | Small worker **0.15–0.30 ms profile budget**; large benefit not isolated; no optimized measurement yet | Pure checked equivalence, no necessary TCB growth. Do not trust a host truncation or change the pinned Nat/runtime. |
| 4 | Reuse checked final canonical state bytes; moderate-to-high linearity/finisher proof work | Small ~**0.07 ms**; large **5–7 ms budget** for one encoding. Retaining bytes can reduce the net saving | Prove exact old finalization, canonical bounds, Commit/Keep and root/response pair; no necessary new host authority. |
| 5 | Pre-exec single-use worker pool, bounded refill; moderate host lifecycle work | Remaining worker **0.46 ms small / 0.53–0.60 ms large** while ready; not a throughput claim | T3 correct artifact/current snapshot/registry delivery, shutdown/invalidation cleanup and setup-failure ordering. Existing one-request isolation retained. |
| 6 | Single-pass private framing, direct typed decode; then compact schema codec; moderate-to-high proof work | Several-ms large-state entry budget exists inside the current **8.64 ms** entry, but net savings unmeasured | Pure refinement/canonicality/provenance proofs. Keep specified public state-size accounting. No unchecked host row/state parser. |
| 7 | Checked unchanged-state flag + `CommitReuse`; substantial native/host bridge work | Much of the **remaining** large read finalization (roughly 8 ms after step 4), plus output-list work; update gains depend on actual non-mutation | Preserve logical success Commit and new paired response; prove unchanged-state invariant and exact current-root reuse. Do not turn success into Keep. |
| 8 | Retained typed state / closed-catalog server, or checked witnessed partial state + proved map/index | Required for eliminating O(database-size) work; **no validated latency estimate toward 0.042 ms** | Major serial ownership/registry/IO/failure/refinement proof work; document any new host projection, versioning or cryptographic assumptions. Indexing is still needed: the current last-key body alone is 0.31 ms at 1,105 rows. |

After steps 1–2, an arithmetic budget is roughly **1.6–1.9 ms small** and
**25–27 ms large**, before source optimizations/pooling. This is a design
projection, not a measured combined implementation. A ready pool plus constant
limit specialization and encoding reuse could bring the small case near the
one-millisecond scale; the large case still needs state-representation work.

Savings are estimates from independent measured components, not measured
cumulative implementations. Do not add removed authentication costs, its hash
cost and its pool cost twice. Any implementation must retain both official
checkers on every admitted Book, all theorem roots, causal negative admission
fixtures, exact current-root authentication, invalidation/no-revival and
failure/cleanup/publication ordering. In particular, include wrong-artifact,
stale registry, revoked credential, tampered authoritative image and
malformed/oversize request cases in the eventual regression gates.

The 0.042 ms PostgreSQL point read is a goal, not an attained or projected
result of these host changes. The measured fresh-process floor alone is much
larger. Even perfect removal of spawning and integrity checks leaves checked
whole-state decode/validation/encoding at millisecond scale. Approaching that
goal needs a checked retained-state or authenticated-local-state architecture,
not compiler/runtime rewriting.

## Reproduction, verification and limits

Start in this worktree with the pinned tools installed as `INSTALL.md`
describes. This session used a local `.tools` symlink to the already pinned
shared installation, and did not modify it. Run from repository root:

```sh
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; make build'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; paper/bench/fixed-clock.sh python3 -B paper/bench/repeated_diagnose.py --calls 100'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; paper/bench/fixed-clock.sh python3 -B paper/bench/repeated_replay.py'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; paper/bench/fixed-clock.sh python3 -B paper/bench/repeated_profile.py'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; paper/bench/fixed-clock.sh python3 -B paper/bench/repeated_refine.py'
flock /tmp/jaydb2-experiments-heavy.lock bash -c 'ulimit -s unlimited; paper/bench/fixed-clock.sh python3 -B paper/bench/repeated_auth_profile.py'
```

The replay tool builds a **scratch Cargo package**, compiling
`paper/bench/repeated-host.rs` with sha2 0.10.9, serde_json 1.0.154 and libc
0.2.191. Production `Cargo.toml`, lockfile and `server/capture.rs` are unchanged.
The scratch build uses offline cached dependencies; install ordinary project
dependencies first if they are not cached. The tool builds hello/echo in
`.build/paper-bench/repeated`. `repeated_profile.py` needs `sudo -n` perf/BPF
access; it waits for a globally attached tracer before launching known worker
children. Its `--bpf-only` mode was used to correct an initial harness-only
probe scope; those empty observations were discarded. The final template
reserves the first startup field as zero; old raw logs retain an invalid
syscall-entry field, explicitly excluded from the evidence summary.

`repeated_refine.py` runs the 15-case matrix, exact state comparisons, seal/fd
exec tests, compiler variants, pipe-size tests, memory/fault observations and
TSC calibration. Extra C, executables, traces and snapshots are scratch files
under `.build/`; the useful tools alone are maintained in `paper/bench/`.
All alternate native builds compile exactly the already-admitted literal C.
No modified Book or unchecked alternate client program was executed.

Successful verification in this research: release build; actual service
initialization and universal preparations accepted by **both checkers**; 400
measured service calls plus warmups and checked setup/control responses; exact
replay root/response validation; ten exact early-denial comparisons in the
15-case matrix; sealed-fd mutation failures and exact fd-exec output; alternate
compiler output equality at both sizes; Python syntax checking and Rust
harness builds. No production or proof files changed.

Final read-only verification at **2026-11-12T13:23:50Z** matched the original policy
on all CPUs: `powersave`, `balance_performance`, and `intel_pstate/no_turbo=0`.
The last experiment's fixed-clock restoration trap also verified that policy.

The full proof/negative-fixture release suite was not rerun for this research
report; production and proof sources are unchanged. The checked fixture builds
and direct rejection matrix validate the paths used here, not a new theorem.
Only one machine/session per service condition was measured. The replay,
uprobes and syscall/perf observations are separate runs with different observer
costs. BPF timestamps include probe overhead; strace syscall wall durations
include blocking and overlap, so their sum is not a decomposition of native
CPU or end-to-end latency. Sampling identifies CPU consumers, not exact pure
semantic invocation counts. No benchmarked implementation of a new codec,
finalizer, authoritative single-pass route or persistent server was created.
