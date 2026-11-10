# Official native execution

Admission passes the same checked Book to official Bend 2 `compile_book`.
The emitted C is compiled literally by `tools/service/stage.mjs` with Clang 19.
There is no C rewriting, replacement runtime, custom Nat/Array representation,
DSO ABI, or derived verifier.

Each call runs that program in a new child process with the official options
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
registration, `Worker.registered_packet`. Private state is decoded once and
kept through every early-error branch. Ordinary request ingress is
`Input.read_message`; prepared execution uses `Resolve.select` with the exact
live registration supplied separately from the original request. Both enter
`Gate.begin`: fresh authentication precedes the statically admitted oracle,
and rejection leaves client program construction suspended.

The oracle binds the frozen source/proof and configuration; concrete execution
also binds the admitted context and canonical arguments, while a universal
prepared certificate specializes to the current values. Its only Accept branch
constructs that checked `Client.program()`. Exact source/elaboration/certificate
binding remains T1; the environment guard does not purport to compare arbitrary
function-valued configurations.

The loop still consumes one `Execution.advance` step at a time, using
`Core.advance`. The stopped branch now calls `Gate.finish`; early branches call
`Gate.early`. Checked `Execution.decision` then selects Commit or Keep and
encodes the exact framed bytes. The unchanged private ABI is
`1 || frame(root) || response` for Commit and `0 || response` for Keep.
Rust obeys this decision after cleanup and optional durable publication.
`WorkerBridge.worker_body_equals_ingress_composition` and
`worker_unified_equals_gate_composition` reuse the existing ExecutionAdapter
proof to connect finite loop results to the theorem's Gate composition.
The actual generated entry, iteration conversion and step equations are also
checked in its admitted Book. Fuel belongs only to the proof, not the native
execution policy.

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
with the actual compiler arguments. The Rust host checks the executable before
every call. A child failure preserves published state. The host publishes only
after receiving and validating complete output and reaping the process.

State and response sizes are checked on the complete proposal; they are not
RAM quotas. There is no program timeout or resource observer. A fatal failure
of the database process can still lose the RAM instance.

## Remaining T3 plumbing obligations

1. Pin valid initial root, configuration, source, tool and executable bytes;
   preserve the exact checked admission tuple and prepared registration.
2. Supply complete original bodies and one current private root, with outer
   framing bounds and FIFO/EOF behavior preserved.
3. Run the same admitted Book through a fresh worker and the exact checked
   step conversion; expose no publication capability to client code.
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
authenticated calls include the actual context and bindings; call completion
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
