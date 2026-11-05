# Bend controller replacement

Work in progress until the validation evidence below is recorded.

Base: `5925c57febd978d44fa24000233647a59e7898a6` (original reference
`9b751fab3c7c349ff473a2d11a7133573b6c4df2`). Accepted prerequisite:
`0f09c55dfff52fe10cd86b18a72a3241c5a92ad5`, merged as
`abc66d6fd70134c1b87a228e95b7b2b0af8be46a`.

## Executable route and scope

`make build` emits and builds the production Bend controller. `./jaydb2` and
`./jaydb2-bend` launch it through `host/launch.mjs`. No Rust controller is run
on this route. `make build-rust-reference` and `./jaydb2-rust-reference` retain
the former controller solely as an explicit differential reference.

The official pinned 2.0.39 TypeScript loader, primary checker, BendTT admission,
compiler and emitted C runtime are unchanged. The native driver is an application
foreign effect registered with the official API, like the existing worker
read/write/iteration effects. It interprets `Exchange` and `Stop`; it does not
parse client frames or proposals or implement a separate language/runtime.

The executed `Controller.bend` functions own frame interpretation, terminal
framing behavior, ordinary/prepared routing, authentication-before-handle
lookup, random handle collision lookup, registration/invalidation, source and
proof linkage, control response bounds, cleanup ordering, execution proposal
checks and publication. The registry lives in Bend `Database.handles`.
`Policy.bend` supplies the actual byte guards and publication function called
by that controller. The OS adapter does not hold the published state or a
client handle registry. Public state bytes cross it transiently only as stdin
for fresh workers and explicit administrator inspection output.

Current route is serial with normal frame/status/value semantics. It supports
CPU `--threads 1..128` (available parallelism capped at 128 by default),
`--configuration`, `--seed`, `--bend-source`, `--bendtt`, and
`--inspect-socket`. Preparation requires a universal certificate and preserves
exact admitted code/proof, compiled executable, all sealed request/public/runtime
artifacts and fresh current-state authentication. Unknown handles and stale
credentials keep their normal precedence. All three canonical byte limits
remain unsigned 64-bit values; no Nat/U32 truncation is used for header limits.

```
flock /tmp/jaydb2-experiments-heavy.lock make build
./jaydb2 --configuration examples/access/Configuration.bend \
  --seed examples/access/Seed.bend --threads 1
```

## Effect inventory and interface

The pinned `Base` has text `Process.run` with mandatory combined output and
elapsed bounds; its contract cannot implement the former binary, no-deadline
worker pipeline. It provides byte file operations and TCP, but the service also
needs directory creation/removal, immutable artifact hashes, cryptographic
random bytes, Unix inspection sockets, subprocess ownership/reaping, concurrent
pipe draining, and (for the later persistence port) protected storage ownership,
file and directory flush and atomic same-filesystem replacement. Those last
durability effects are not implemented or claimed in this milestone.

The minimal `Effects.drive` foreign effect exchanges length-prefixed octets
with a private Node pipe. A command is one opcode plus binary fields. Responses
are `1 || result` or `0 || UTF8(error_code)`. Fields use the existing exact
`Transport` two-block framing. No client values are decoded by the adapter.
There is no production subprocess timeout or output truncation.

| Opcode | OS responsibility |
| --- | --- |
| 0 | Freeze/check/build initial and authenticate workers; report three u64 limits |
| 1 | Read up to a Bend-selected exact byte count from client stdin |
| 2 | Fully write Bend-selected response bytes, report delivery errors |
| 3 | Allocate a private request directory and opaque OS resource ID |
| 4 | Store exact public admission metadata, run existing official staging, load/hash executable; return limits/certificate mode |
| 5 | Validate executable hash, run fresh CPU child with binary pipes, return output only after reaping and all pipe cleanup |
| 6 | Seal request, public environment and runtime regular files by hash |
| 7 | Remove a Bend-selected directory/resource |
| 8 | Obtain 32 cryptographically random bytes as hexadecimal ASCII |
| 9 | Serialize Bend-selected inspection event and exact state bytes to administrator socket |
| 11 | Verify all sealed regular files, reject missing/changed/symlink artifacts |
| 12 | Emit a Bend-selected technical diagnostic, preserving OS detail |

OS IDs address adapter-owned files and executables, not prepared public handles.
The adapter's staging mode conversion merely selects an existing staging effect;
Bend chooses the operation, checks initialized-limit agreement and requires
universal mode before registration. Compilation receives code/proof/generated
instance/bindings only, never current state or the raw credential packet. The
fresh action worker independently analyzes/authenticates the same state/request.

The launch adapter checks the Bend executable hash. Environment identity now
includes the controller executable and all host Bend/C/adapter sources. The
legacy Rust route retains its `/proc/parent/exe` binding. Toolchain source is a
read-only shared `.tools` symlink; all builds, default temporary directories and
validation logs are local to this worktree.

## Proof linkage and trust

`host/VERIFY.bend` imports the exact production `Policy` and `Controller`
functions. Generic proofs cover preservation of the old state on rejected and
nonpublishing proposals, exact pair replacement on a publishing proposal,
state bound on ready `check_state` results, response bound and empty trailing
bytes on ready `checked_response` results, and inability to pass a false guard.
Closed checks cover incomplete/high-word/exact-boundary frame headers, changed
configuration limits, concrete preparation refusal and malformed publication
markers. The existing transport proof establishes packet split/join exactness;
accepted preprocessing proof establishes exact output equivalence of the
single-pass route. A negative test mutates the executed publication function
and requires its linked proof to fail.

These are byte/control refinement proofs, not a proof of the OS or the entire
new controller protocol. In particular, actual subprocess/filesystem/hash
results, read/write/inspection byte correspondence, C driver interpretation,
resource identity, cleanup/reaping, Node/V8 allocation behavior and protected
local files remain trusted effects. The original worker admission and prefix-law
proofs are retained; these host lemmas do not replace them with final-state
validation or assert that arbitrary bytes are valid states. Publication safety
still requires the freshly admitted official worker's exact input/output and
frozen dependency correspondence. No checksum is an authorization proof.

## Validation

Pending focused locked run; exact results will replace this paragraph.

## Costs and remaining scope

No performance claim is made. Each controller/adapter RPC copies bytes through
Bend lists and native/Node buffers. It preserves no-deadline, untruncated process
semantics, so physical memory exhaustion and nontermination remain possible,
as in the anchor. Native Nat immediates have the official 48-bit addressability
limit; stored signed 64-bit values remain encoded as two U32 halves. This does
not narrow the stored integer domain or three logical limits.

This milestone targets the anchor ordinary/prepared protocol plus accepted
preprocessing. The accepted scheduling interface was inspected:
`SerialService.execute` completes all cleanup and `publish` is fallible, with
fatal publication producing no response or further dispatch. Queuing,
persistence, timing/quotas, certified read concurrency and GPU execution are
not claimed on the Bend route until their accepted contracts are ported and
validated. In particular this route currently reads one frame at a time, has
no durable commit, and intentionally does not accept flags for those unported
extensions. No advanced-library dependency is needed.
