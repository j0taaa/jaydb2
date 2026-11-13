# Official native execution

Admission passes the same checked Book to official Bend 2 `compile_book`.
The emitted C is compiled literally by `tools/service/stage.mjs` with Clang 19.
There is no C rewriting, replacement runtime, custom Nat/Array representation,
DSO ABI, or derived verifier.

Each call runs that program in a single-use child process with the official options
`+RTS --threads N --gpu off -RTS`. The host selects its available CPU parallelism
by default, capped at 128 workers, and falls back to one worker if detection
fails. The host's `--threads N` option accepts 1–128 to override that selection.
The selection applies to initialization, decoding within authentication, ordinary
execution, and prepared-program execution. Independent Bend computations can
run in parallel; the host serves requests and publishes state serially.
Published state belongs to the host.
Input and output travel through pipes; state is not written to the compilation
directory. The process exits and the operating system releases its resources
before the host accepts a proposal for publication.

## Checked worker path

The generated closed entry calls `Worker.packet` or, for a live prepared
registration, `Worker.routed_bytes` (proved equal on every input to the original
`Worker.routed_packet` metadata-preserving lift of `Worker.registered_packet`).
Private framing fuses octet validation with cutting and constructs each prefix
in order, without a reverse accumulator. The prepared outer separator validates
its registry prefix only; the inner separator validates the untouched root/body
suffix before decoding. `TransportScan.separate_refines_reference` proves the
full separator equals the previous parser on every U32 list, and
`WorkerBridge.routed_bytes_equals_original_packet` proves that deferring the
outer suffix scan preserves the complete worker result, including malformed
private packets. A prefix-only result is never by itself a validated packet.
These are pure source refinements with no new T1–T3 premise or byte-format change.
Private state is decoded once and kept through every early-error branch. Ordinary request ingress is
`Input.read_message`; prepared execution uses `Resolve.select` with the exact
live registration supplied separately from the original request. Both enter
`Gate.begin`: fresh authentication precedes the statically admitted oracle,
and rejection leaves client program construction suspended.

The oracle binds the frozen source/proof and configuration; concrete execution
also binds the admitted context and structural arguments, while a universal
prepared certificate specializes to the current values. Its only Accept branch
constructs that checked `Client.program()`. The checked Book proves `generated_oracle_sound` for this exact oracle.
Checker soundness, source/purity audit and exact source/Book/artifact binding
remain T1; the environment guard does not purport to compare arbitrary
function-valued configurations.

The loop still consumes one `Execution.advance` step at a time, using
`Core.advance`. The stopped branch calls the optimized `Execution.finish`;
early branches call `Gate.early`. The stopped result is proved equal to the
reference `Gate.finish` / `Execution.decision` composition, including its
Commit/Keep selection and exact framed bytes. The underlying private decision ABI remains
`1 || frame(root) || response` for Commit and `0 || response` for Keep.
Ordinary workers emit that decision directly. Prepared workers emit
`6 || frame(environment) || optional(route) || optional(principal) || artifact_match || authentication_ready || decision`,
where `frame(environment)` is `u64be(utf8_length) || utf8`, and `optional`
is `0` for None or `1 || u64be(utf8_length) || utf8` for Some,
and both flags are exactly `0` or `1`. `Some{""}` remains distinct from None.
`WorkerResult.attach/advance` retain checked metadata beside the unchanged
Execution state and encode it only at completion. The actual generated
conversion/step laws use this adapter for prepared workers; the original
Execution driver remains used for ordinary requests. `WorkerBridge` proves
finite driver correspondence and exact underlying decision projection.
Rust obeys this decision after cleanup and optional durable publication.

The stopped-machine adapter retains the exact canonical state bytes used for
the state-size check and supplies them to Commit framing, avoiding a second
state encoding. `Execution.finish_equals_reference` proves exact equality to
the original Gate/Core preparation and decision serialization on all inputs.
`LimitWords.convert_equals_reference` checks the precomputed 65,536-byte u64
ceiling against `Bytes.nat64`; other limits keep that reference conversion.
Staging relocates the limit witness's proof dependencies into the admitted Book.
Neither optimization changes the ABI, foreign effects, compiler/runtime or
T1–T3 duties. Equal-root success still emits Commit with its new response.
`WorkerBridge.worker_body_equals_ingress_composition` and
`worker_unified_equals_gate_composition` reuse the existing ExecutionAdapter
proof to connect finite loop results to the theorem's Gate composition.
The actual generated entry, iteration conversion and step equations are also
checked in its admitted Book. Fuel belongs only to the proof, not the native
execution policy.

For a bounded canonical prepared-execute body the host may tentatively locate
an admitted artifact. Only the worker's checked request decoding, fresh
current-root authentication and complete live-registry lookup select the logical
call. Checked metadata includes its frozen environment, raw handle and selected source/proof match;
Rust must compare the environment/handle and require both flags before accepting
a proposal. Missing/doubtful candidates,
integrity failure, malformed output, child failure or checked mismatch discard
that result and retry the original authenticator/dispatch path. All request/root/
registry bytes stay unchanged. A candidate worker cannot publish. Retry preserves
early-denial precedence and the authenticator principal after a worker crash,
at the cost of potentially running two private workers. Intermediate candidate
failures are discarded; only the final authoritative result or failure determines
publication and delivery. T3 explicitly trusts
metadata framing/comparison and retry-before-publication, not host authentication.

The readiness flag is the checked projection of the original
`Messages.authentication` result: tags 0/1 are ready, tag 2 is not. This retains
the original argument reification and metadata-frame failure discriminator
inside the worker, rather than assuming those computations cannot fail. An
unready result is discarded before decision parsing/publication and retries the
original path, regardless of any enclosed decision/principal. The candidate
may already have run admitted client code that the original tag-2 path would
not have run. Its universal certificate covers that execution and observations;
client code remains pure, has no host effects or publication capability, and
the result is discarded. Extra work can still delay or exhaust service.

## Application effects

`effects.bend` declares the kernel's only trusted effects. `effects.c`
implements them through Bend's documented foreign mechanism (`io_eff`):

- `read` receives bytes until EOF and builds the list with official `io_list`.
- `write` uses official `io_cbuf` and `io_out`, without UTF-8 conversion of bytes.
- `loop` applies a closed step to the linear state cell until completion.

The Bend wrapper carries that cell as a `Unit -> StateExecution` function.
This uses the official function BOX and transfers the capture once; it neither
reconstructs the state's internal layout nor changes the compiler to force a
representation. The step function is closed and fixed by the host. Client
code receives neither these effects nor the state cell.

## Identity and failures

The manifest records SHA-256 of literal C, the executable, and Clang, together
with the actual compiler arguments. At load the Rust host copies the released
ELF into a CLOEXEC memfd, installs F_SEAL_WRITE/GROW/SHRINK/SEAL, checks
F_GET_SEALS for at least those four seals and hashes the sealed image against
executableSha256. Additional kernel seals, including F_SEAL_EXEC, are permitted.
Creation requests MFD_EXEC; only EINVAL retries without the flag for older
kernels. vm.memfd_noexec=1 is supported by explicit MFD_EXEC; policy 2 can forbid
executable memfds and then fails closed with a HOST_NATIVE policy diagnostic.
A returned fd without execute permission also refuses load. No kernel policy is
changed. See [Linux memfd policy](https://www.kernel.org/doc/html/latest/userspace-api/mfd_noexec.html). Sealing or
verification failure refuses load. It owns that fd for the program lifetime
and retains it above fd 2 so child standard-pipe setup cannot replace it.
A borrowed launch wrapper enforces Image lifetime through spawn/capture without
exposing an extractable Command. It launches /proc/self/fd/N with ordinary Command::spawn (no pre_exec, retaining
posix_spawn). This replaces hash-before-every-call and prepared staging-file
rereads with verification once and trusted kernel seal enforcement. Staging
source/C/manifest/executable copies are diagnostic after admission. Future
compilations still compare all frozen public/runtime inputs and environment
metadata against in-memory originals before invoking staging; both official
checkers and existing release gates remain mandatory. Host-owned compilation
storage remains trusted against changes during validation/use.

The dynamic loader, libc, libm, loader configuration and inherited loader
variables remain trusted as before; the old per-call checks did not protect
those inputs either. Static linking was not adopted; compile policy and
literal official emitted C remain unchanged.

At most eight images process-wide, including the authenticator, each have one
idle, already-spawned single-use child and a background refill thread. Pool
permits are first-come and released only after join/kill/reap cleanup. Additional
registrations use fresh selected spawns; refill-thread startup failure also leaves
the program on that fresh path. This caps pool processes/threads/pipes, while
registrations still retain their admitted memfds. Open stdin leaves the checked
entry waiting without any state, credential, registry or request. Only selection
delivers the current packet and EOF. A process is never reused: capture,
complete output, exit, reaping and publication ordering are unchanged. The
pool preserves per-call process isolation; it moves startup earlier. Background
refill receives only the immutable image and fixed runtime thread count and
cannot publish or change the serial root/registry. It preserves BENDRTS="",
BEND_NO_TELEMETRY=1 and +RTS --threads N --gpu off -RTS.

A dead idle child is reaped and selection falls back to a fresh spawn. A child
dying after the liveness check is an ordinary native/transport failure; no
request is retried by the pool after packet delivery. [T3 duty 3](../proof/README.md#trusted-base)
separately requires discarding and retrying a tentative routed candidate before
publication; that host retry can follow candidate packet delivery or failure.
Refill spawn failure leaves the slot empty and the next selection attempts a fresh spawn. Invalidation and shutdown
join refill, kill and reap idle children. Each pooled image retains at most
one idle child, three pipes, one memfd and one refill thread (plus the selected
single-use child while active), under the eight-image global pool cap. There
is no total-memory or registration-count quota. Native virtual reservations
remain those of the pinned runtime. Pipe-thread startup failure remains fatal:
waiting threads are joined and an already selected idle child is killed/reaped
before unwinding, with no packet delivered and no new helper launched. Error
replies use the same thread-dependent transport, so continued service cannot
reliably report that exhaustion. Fatal host/resource failures already fall
outside the response guarantee (T3 duty 5).

A child failure preserves published state. The host publishes only
after receiving and validating complete output and reaping the process.

State and response sizes are checked on the complete proposal; they are not
RAM quotas. There is no program timeout or resource observer. A fatal failure
of the database process can still lose the RAM instance.

## Remaining T3 plumbing obligations

1. Pin valid initial root, configuration, source, tool and executable bytes;
   preserve the exact checked admission tuple and prepared registration.
2. Supply complete original bodies and one current private root, with outer
   framing bounds and FIFO/EOF behavior preserved.
3. Run the same admitted Book through a single-use worker and the exact checked
   step conversion; bind idle children to the exact sealed image/runtime policy,
   deliver current data only at selection, and clean up/refill as described above.
   Expose no publication capability to client code.
4. Collect complete packets, reap children and finish rollback-capable cleanup
   before accepting Commit; technical failures before commit preserve the root.
5. Physically publish only Commit's exact root/response pair and deliver the
   returned bytes. After commit, delivery failure preserves publication.
6. Keep persistence, registry control receipts, timing and inspection ordering
   faithful to their separate host specifications. They are not proved by the
   core worker bridge. Compiler/runtime/foreign-loop preservation remains T2.

## Optional administrator inspection

`--inspect-socket ADMIN_SOCKET` enables a diagnostic administrator output over
a Unix socket, separate from the client protocol. The host sends JSON metadata
and canonical published-state bytes, each with an 8-byte length header.
Initialization includes frozen public sources, the seed, and limits;
ordinary authenticated calls include the actual context and bindings;
prepared calls emit checked-resolution metadata only after the candidate result
passes identity checks (the original fallback emits it before worker launch); call completion
includes published state and any diagnostic. Workers do not inherit the
descriptor. Observer failures disable this output without changing the call's
response or publication.

The [web demonstration](../demo/README.md) uses this capability to show the
database to its administrator. It exposes data kept private by the ordinary
interface and is outside the service-contract proofs' scope. It does not
change client-program permissions. Normal CLI mode does not enable inspection.

## Observed official limitations

The official toolchain has limitations JayDB does not work around. In
particular, Bend 2.0.39's immediate native path rejects the observed `Nat`
calculation above `2^48-1`, and the native `Array` path requires the balanced
tree representation. Former 129-bit Nat and unbalanced Array cases are now
explicit toolchain-failure controls, not declared supported features. F32,
captured functions within the supported domain, bytes, and iteration are
exercised with actual official C.

These checks do not establish general compiler correspondence or discharge
T1–T3. JayDB does not modify Bend to claim either result.

Ordinary request compilation uses Clang `-O0` to reduce its per-call compilation
latency. Initialization, authentication and reusable prepared workers retain
`-O2`; prepared execution amortizes that optimization cost. Both paths compile
the literal official C with the same runtime and checker modes. Programs with
substantial computation should use prepared execution to retain optimized C.
