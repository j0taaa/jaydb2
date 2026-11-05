# Service with three logical limits

Administrator configuration and dependencies are public. The chosen seed file
is private and participates only in initialization; public configuration may
not import it, including through another name or path to the same file.

The active entry is `./jaydb2` → `host/Controller.bend`, using byte effects in
`host/os.mjs` and existing `tools/service/stage.mjs`. The host decisions execute
in Bend, admission and compilation are coordinated by Node, and each
compiled program uses the official Bend runtime. Python is not part of service
execution. Configuration contains only `message`, `state`, and `response`,
measured in canonical bytes. Equality with a ceiling is allowed. There is no
physical budget, observer, or execution deadline.

## Call path

The optional [prepared-program extension](PREPARED_PROGRAMS.md) checks a
universal certificate and compiles once, then reuses an instance-local native
worker with current authentication, state, and arguments. Its controls and
receipts have a separate protocol boundary from the ordinary path below.

1. The host reads framing and checks message size.
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

Compilation directories receive code, proofs, and public admission data, never
private state. The seed participates only in initialization and is removed
before serving. Per-call state crosses pipes in RAM, never a temporary input
file.

## Ownership and failures

The OS adapter owns each process and its pipes. It feeds binary input while
draining stdout/stderr concurrently, and reports completion only after reaping
and all pipe cleanup. Bend then chooses whether to validate and publish.
The [Bend-host report](../../experiments/bend-host/REPORT.md) specifies the byte
effect interface and the actual controller proof boundary.

There is no DSO, lease, `dlclose`, or replacement runtime. Child exit
releases its resources. A child failure returns `failure` without publishing, and
the host can serve the next call. Uncertain ownership ends use of the instance
without repeating a potentially consumed operation.

The profile is a serial Linux CLI with trusted tools and host. Its default
volatile mode loses RAM data when the host dies. Optional complete-image
persistence is available in the separately built Rust reference (not yet
ported to the standalone Bend route):

```sh
./jaydb2-rust-reference --configuration examples/access/Configuration.bend \
  --seed examples/access/Seed.bend --storage DATABASE --storage-mode create
./jaydb2-rust-reference --configuration examples/access/Configuration.bend \
  --storage DATABASE --storage-mode open
```

Create requires a new directory with an existing parent; open requires the
authoritative snapshot and forbids `--seed`. A single owner holds an OS lock.
Every successful state proposal writes and synchronizes a complete temporary
image, atomically replaces the authoritative image, and synchronizes the
directory before RAM publication and response delivery. Errors from replacement
onward stop the instance with no response, since rollback may be false. Missing,
corrupt or incompatible images stop startup; no seed or older image is used as
fallback. Users and all tables survive; prepared handles do not.

Recovery requires the exact same environment, including actual controller
executable bytes. Protect the storage directory and preserve that executable
and its sources/tooling. The [persistence report](../../experiments/persistence/REPORT.md)
states the serialization/recovery proof, OS/filesystem assumptions, fault tests
and limitations. Process death tests do not establish hardware power-loss safety.

The Node helper uses only a public stack-size option, without an addon or Bend
change. The stage uses Clang 19 with `--no-default-config`; native programs
receive the official `--threads N --gpu off` options. CPU workers default to
the host's available parallelism, capped at 128 (one if detection fails).
The launcher and native worker adapter clear inherited `BENDRTS`; service
options determine runtime behavior, including the controller's CPU-only mode.
The host's `--threads N` option accepts 1–128 and applies to all native stages,
including prepared execution. Requests and state publication remain serial.
Installation of these tools is part of the trusted environment.

## Verification

Bend proofs cover the pure machine, certificates, and their consequences for
authentication, operations, observations, and preparation/publication in the
model. Administrator laws remain mandatory at every prefix, including before
a refusal or failure.

The execution's trusted base includes pinned official tools, Node, Clang, the
operating system, the byte effect driver and adapters, and worker effects.
`host/VERIFY.bend` checks actual Bend proposal guards and publication functions.
It does not establish OS refinement or the entire new controller protocol.
Administrator/client proofs remain mandatory; hashes are integrity checks.

`make test-host` executes the actual native controller against injected byte
operations and checks OS adapter boundaries. `make test-native` compiles
worker effects and exercises representations. `make test-integration` admits,
compiles and executes real Bend transactions. The explicit Rust reference is
used by `tests.bend_host.test_differential`; it is never invoked by production.
See the [law map](../../proof/SERVICE_CONTRACT.md) and the Bend-host report for
remaining integration assumptions. Building and testing do not imply the
full proof aggregates ran in both checkers.

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
