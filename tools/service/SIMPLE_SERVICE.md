# Service with three logical limits

Administrator configuration and dependencies are public. The chosen seed file
is private and participates only in initialization; public configuration may
not import it, including through another name or path to the same file.

The active entry is `./jaydb2` → `server/main.rs` → `tools/service/stage.mjs`.
The host is Rust, admission and compilation are coordinated by Node, and each
compiled program uses the official Bend runtime. Python is not part of service
execution. Configuration contains only `message`, `state`, and `response`,
measured in canonical bytes. Equality with a ceiling is allowed. There is no
total-process memory budget, observer, or execution deadline.

## Call path

The optional [prepared-program extension](PREPARED_PROGRAMS.md) checks a
universal certificate and compiles once, then reuses an instance-local native
worker with current authentication, state, and arguments. Its controls and
receipts have a separate protocol boundary from the ordinary path below.

1. A bounded reader receives complete frames and checks message size. It
   enqueues FIFO bodies without inspecting credentials or programs. One
   coordinator selects a request for service against the current snapshot.
2. One official native Bend authenticator decodes and authenticates against
   published state. `Input.analyze` preserves decode errors before checking
   credentials, so no separate decode child or decoder compilation is needed.
3. Admission checks source, dependencies, and proof with official tools against
   the actual configuration, context, and arguments.
4. The same checked Book is compiled by the official compiler. The stage only
   invokes Clang on literal C and records C and executable hashes.
5. The program runs in a fresh native child process on CPU with GPU disabled.
   Its proposal is private. It still runs `Input.analyze` on the same actual
   state/request packet, obtaining its current authenticated context and
   arguments. The Codec remains the compiled Bend program.
6. The host receives all output, reaps the process, validates state/response,
   and removes the temporary directory before accepting publication.
7. Success replaces the serial host's `Published { state, response }` pair.
   A refusal or earlier failure preserves the previous publication.
8. Delivery follows. A delivery failure preserves the published pair and closes
   the channel without automatic retry or deduplication.

`SerialService::execute` covers selection/service start through complete
proposal/response preparation and child cleanup. `SerialService::publish`
owns publication; its successful return marks response-ready. It is fallible
so a durability adapter can terminate without a response on uncertain commit.
The coordinator writes and flushes that response before selecting more work.
Prepared registry mutations remain inside the same exclusively owned service.
No identity is computed/cached by the framing reader.

Queue reservations include a body currently being read: at most 8 items and
`max(min(message limit, isize::MAX), 1 MiB)` body bytes, plus one header and one terminal slot.
There is one additional active request of at most the message limit, and one
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

The profile is a serial Linux CLI with trusted tools and host. It does not
promise recovery from fatal failure or database death. Losing the host can
lose its RAM data without a response.

The Node helper uses only a public stack-size option, without an addon or Bend
change. The stage uses Clang 19 with `--no-default-config`; native programs
receive the official `--threads N --gpu off` options. CPU workers default to
the host's available parallelism, capped at 128 (one if detection fails).
The host's `--threads N` option accepts 1–128 and applies to all native stages,
including prepared execution. Requests and state publication remain serial.
Installation of these tools is part of the trusted environment.

## Verification

Bend proofs cover the pure machine, certificates, and their consequences for
authentication, operations, observations, and preparation/publication in the
model. Administrator laws remain mandatory at every prefix, including before
a refusal or failure.

The execution's trusted base includes pinned official tools, Node, Clang, the
operating system, and JayDB integration code: the Rust controller, Node
preparation/admission, and `native/effects.c`. This code connects checked
sources, arguments, pipes, and concrete publication; its bodies are not
formally checked by Bend's checkers. This does not permit dispensing with a
client proof or replacing laws with final-result tests.

Rust tests cover publication, rollback, and framing. `make test-native`
compiles official C and exercises effects, representation, and actual
toolchain limits. `make test-integration` admits, compiles, and executes real
Bend transactions. Hashes and tests identify artifacts and support the cases
executed; they do not replace a proof of the complete executable's eight laws.

`make build`, `make verify-contract`, `make verify`, and `make test` are separate
steps: building or passing tests does not imply that both checkers ran on the
proof aggregates. `proof/ContractService.bend`, included by `make verify`,
composes exactly `Contract(a,k)` for the kernel and serial protocol under the
explicit tool and integration contracts. The [law map](../../proof/SERVICE_CONTRACT.md)
identifies assumptions; the Rust/Node/C bridge remains trusted and supported
by review/tests rather than a mechanized proof of those components.

## Rust helper pipe startup

Rust helper capture uses fallible scoped pipe-thread creation. Its child guard
lives inside the scope closure so every early return or Rust unwind kills and
reaps the direct child BEFORE implicit joins of already-started pipe threads.
This also releases a writer blocked on stdin and readers blocked on output.
Normal successful captures still drain all binary bytes and wait for the child.

A pipe-thread startup failure retains the existing fatal policy, now raised only
after child cleanup and pipe joins. It cannot become a recoverable response or
allow later queued requests to start. Tests inject errors and unwinding before
each of the three pipe-thread creations and check actual child reaping. This
is OS-boundary evidence, not a new mechanized proof or a hard deadline. On the
Bend-host branch this describes the retained Rust reference only.
