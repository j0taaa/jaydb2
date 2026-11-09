# Official native execution

Admission passes the same checked Book to official Bend 2 `compile_book`.
The emitted C is compiled literally by `tools/service/stage.mjs` with Clang 19.
There is no C rewriting, replacement runtime, custom Nat/Array representation,
DSO ABI, or derived verifier.

Each call runs that program in a new child process with the official options
`+RTS --threads N --gpu off -RTS` by default. The opt-in
[CUDA backend](../experiments/gpu/REPORT.md) uses required `--gpu <MiB>MB`
for execution workers after prebuilding their `.gpu` artifact; preprocessing
continues with GPU disabled. The host selects its available CPU parallelism
by default, capped at 128 workers, and falls back to one worker if detection
fails. The host's `--threads N` option accepts 1–128 to override that selection.
The selection applies to initialization, decoding within authentication, ordinary
execution, and prepared-program execution. Independent Bend computations can
run in parallel; the host serves requests and publishes state serially.
Published state belongs to the host.
Input and output travel through pipes; state is not written to the compilation
directory. The process exits and the operating system releases its resources
before the host accepts a proposal for publication.

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

These checks do not establish general compiler correspondence or the complete
executable's `Contract`. JayDB does not modify Bend to claim either result.
