# Official native execution

Admission passes the same checked Book to official Bend 2 `compile_book`.
The emitted C is compiled literally by `tools/service/stage.mjs` with Clang 19.
There is no C rewriting, replacement runtime, custom Nat/Array representation,
DSO ABI, or derived verifier.

Prepared programs run in persistent native workers. The host starts them on
demand and caches idle workers by handle. Direct calls compile a concrete
worker that serves one request and exits. Stdin/stdout serves one FIFO client
session, while `--listen SOCKET` allows concurrent sessions. The host owns
state, transaction overlays and publication.

Native processes use the official options `+RTS --threads N --gpu off -RTS`
by default. One execution slot defaults to available CPU parallelism capped
at 128, with a fallback of one. Concurrent execution defaults to one native
thread per process. `--threads N` sets 1–128 threads. Experimental
`--gpu MiB` gives submitted workers the corresponding official option, for
example `--gpu 512MB`, and uses one execution slot.

## Checked worker path

`tools/service/stage.mjs` builds `live-execute` and `live-prepare`. The
generated closed entry calls `Remote.packet` or `Remote.registered_packet`.
The worker decodes the original request and sends its credential to the host.
It checks the returned user with `D.authenticate`. Prepared execution then
resolves the supplied controller-issued entry. The checked oracle binds the
exact source, proof and configuration. A concrete call also binds its admitted
context and arguments. A universal prepared certificate specializes to the
actual call.

`Remote.admitted` starts the program and `Remote.run` advances its Action
tree. Each Access sends an operation and suspends the continuation until an
answer arrives. The host uses the transaction's versioned snapshot plus its own
writes. Bend checks the response. The host validates the candidate state for
success proposals and gives state errors priority over response errors.
[The remote refinement proofs](../proof/README.md#live-worker-refinement)
connect representable exchanges to the contract interpreter.

## Live worker ABI

Each private frame is `u64be(payload length) || payload`. A direct request
payload is the original body. A prepared request payload is a length-framed
registry containing the selected entry, followed by the original body.
One tag identifies each worker frame.

| Tag | Payload after the tag |
| --- | --- |
| `0x02` | Ordered operation record. The host sends the ordered answer record in its own untagged frame. |
| `0x01` | Framed public success response, pending host validation and commit. |
| `0x03` | Framed response-check error after a success proposal, subject to host state checks. |
| `0x00` | Framed public response. Discard private writes. |

Operation records have a 1 GiB payload bound excluding the tag. The state
limit applies to publication. The ordered fields and their canonical value
encodings are specified in the [live engine ABI](../docs/live-engine.md#2-remote-worker-abi-srcremotebend-nativeeffects).

## Application effects

The live wrapper uses `Native.serve`, a foreign effect in `effects.c`.
It reads frames with stdio and writes them with Bend's byte IO, flushing
each frame. The closed step carries a pending continuation as a one-use
function capture and resumes it with the host's reply. EOF between requests
ends a worker cleanly. A truncated exchange or inconsistent continuation
fails the worker. The startup and control helpers use the separate
`read` and `write` effects. Submitted programs cannot call these effects.

## Identity and failures

Stage receipts record hashes of emitted C, the executable and the compiler
with its arguments. Rust validates executable identity at launch. For
prepared workers it checks the sealed files at spawn. Idle CPU workers reuse
their loaded code. CUDA workers retain pre- and post-exchange artifact checks.
The host reaps a direct worker and removes its request directory before
publication. A failed exchange discards the transaction and retires its worker.

The three canonical size limits govern message, published state and response
bytes. Execution has no deadline or total memory quota.

## Remaining T3 plumbing obligations

1. Bind the checked Book, its epoch and admission tuple to the loaded code.
   Preserve the original request and its selected prepared entry.
2. Answer authentication from the attempt's snapshot and each operation from
   the working transaction. Preserve the framed ABI and `D.operate` semantics.
3. Check final frames, retire failed workers, and complete required artifact
   checks and direct-worker cleanup.
4. Validate write conflicts and state conditions, then publish only successful
   transactions. Sync WAL batches before durable publication and deliver the
   ready response in session order.
5. Keep registry changes, migration cutover, recovery and observer output
   faithful to the [numbered host duties](../proof/README.md#trusted-base).

Compiler and runtime preservation remain T2. The C effect, Rust bridge and
physical publication remain trusted.

## Optional administrator inspection

`--inspect-socket ADMIN_SOCKET` enables a diagnostic administrator output over
a Unix socket, separate from the client protocol. The host sends JSON metadata
and canonical published-state bytes, each with an 8-byte length header.
Initialization includes frozen public sources, limits and the seed on create
or volatile startup. Execution can emit generated bindings or prepared source
identity. Completion includes a published snapshot and any diagnostic.
Metadata includes the snapshot LSN and links request events by request ID. Workers do not inherit the
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
