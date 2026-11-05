# JayDB2

An experimental RAM database that executes Bend programs accompanied by proofs
against administrator laws. It authenticates each call against published
state, works on a private proposal, and publishes complete state and response
with a single reference replacement. Requests are served serially over
stdin/stdout, with code emitted by the official compiler.

Each call runs in a native child process. The host retains published state and
accepts only the helper's complete result before publishing a proposal. C
emitted by the official compiler is not rewritten to create a custom runtime.

The contract has **three canonical size limits: message, state, and response**.
There is no custom physical budget, memory observer, or per-stage deadline.
A fatal failure can terminate the instance and lose its RAM data.

## Installation

Execution profile: Linux x86_64, Node 24, and Clang 19. The controller is a Rust
binary; Python is used only for development tools, tests, and example clients.

The Node helper uses `--stack_size=65536` and an unlimited soft stack limit.
The launcher requires an already unlimited Linux hard stack limit; it does not
change Node or Bend sources.

Follow the [installation and first-session guide](INSTALL.md). It installs
tools locally and uses the unpatched BendTT distributed with the experimental
release. After installation:

```sh
make demo
```

This runs the [credential-change application](examples/access/README.md) on the
real server and shows five JSON responses, including publication,
authentication, and refusal rollback. State exists only for that session.

To try the same real database in a browser, run `make demo-web` and open
**http://localhost:8094**. The [web demonstration](demo/README.md) forwards
operations to a real JayDB2 instance per session, with authentication, Bend
proof admission, publication, and rollback. State stays in RAM; refreshing
retains the instance, and restarting reloads the seed. The workbench lets you
edit code and proofs, inspect schema/laws/sources, and watch published state
live through optional administrator inspection outside the ordinary client
interface and service-contract proofs. The hosted version is available at
**https://jaydb2-demo.jaypussy.site**.

The distribution is **official Bend 2.0.39**. The five official sources and
binaries are identified in `tools/admission/toolchain.lock.json`. On Linux
x86_64 the Bend executable has SHA-256
`2ec160fa4486d33aff51e9eedcc294d6b531dc10c279c00b0c00685dae2045cd`;
the original BendTT has SHA-256
`e365eba1741602bb45261aa0eb6bd2c6f5db885d4b9d4cd603a27bc3c5a9ed18`.

JayDB has no modified frontend, translator, compiler, or BendTT kernel.
Official TypeScript modules are loaded only by stripping TypeScript syntax
with Node. Installation does not build a derived verifier, V8 addon, or adapted
source cache. Official-tool capabilities and limitations remain unchanged.

`server/main.rs` retains published state in RAM and serves frames serially.
Native Bend computation uses the CPU parallelism available to the host by
default, capped at the official runtime's 128 workers. Use `--threads N` to
choose 1–128 workers per native program, or `--threads 1` for single-threaded
computation. Independent work must be expressed in the Bend program to benefit.
GPU support is opt-in: `--gpu 512` requires CUDA for explicit `function!(...)`
calls, with a 512 MiB corpus; the default is `--gpu off`. CPU preprocessing
remains unchanged. See the [GPU experiment](experiments/gpu/REPORT.md) for
requirements, sealed artifacts, failure behavior, examples and measurements.
The Node helper freezes the public environment and verifies and compiles
workers; the seed appears only in initialization compilation. Each worker
receives bytes through pipes and exits before a complete proposal replaces
published state. Server execution does not load Python.

## Client

```sh
python3 tools/client.py --code examples/no-observations/Client.bend \
  --proof examples/no-observations/ClientProof.bend --credential demo
```

This writes a framed canonical message. `python3 tools/client.py --decode`
reads a sequence of responses and prints one JSON line per response.
Configuration and dependencies are public and immutable; seed and current
state remain private.

The optional [prepared-program protocol](tools/service/PREPARED_PROGRAMS.md)
admits a universally certified program once and returns an instance-local
handle for repeated native execution with fresh authentication and arguments.
Use `--prepare`, `--handle`, or `--invalidate` with the Python client. Concrete
per-call proofs keep their existing route. Control receipts and handle
resolution extend the ordinary protocol and have a separate integration scope.

The optional [Bend query library](library/README.md) composes selected-field
reads, filtering/projection and sequential row writes over existing operations.
It adds no database primitive or policy and is not required by client programs.
Run `make test-library` for its real task application flow.

Current `main` uses English-only public names: request fields are
`arguments`, `code`, `credential`, and `proof`; responses use `status` and
`value`; logical limits are `message`, `state`, and `response`; user records
use `credential`, `id`, and `kind`. CLI options, Bend symbols, and module paths
are also English. Clients and application sources using the former names must
migrate; there are no legacy aliases. The binary tag and framing format is
unchanged, but renamed record fields and status values are an API break.

## Verification

```sh
make verify-contract
make verify
make test
```

`make verify` checks the general and optional-library aggregates in both official modes and six
causal mutations. `make test` covers boundaries those proofs do not check:
same-Book admission/emission, execution, publication/rollback, and framing.
Logs, compiled C, and snapshots are not versioned as parallel suites.
Historical results obtained with removed adapters do not attest the current
official path.

The [general proofs](proof/README.md) include canonical Codec equivalence.
[Admission](tools/admission/README.md) uses official frontend, Safe, and BendTT
without rewriting proofs to widen the accepted fragment.
`ContractService.contract_of_service` composes the eight laws for the kernel
and serial protocol under the [explicit tool and integration contracts](proof/SERVICE_CONTRACT.md).
The Rust/Node/C bridge is supported by review and tests; those components and
the compiler have no mechanized proof here.

The [specification](SPECIFICATION.md), [Bend contract](contract/README.md),
[service](tools/service/SIMPLE_SERVICE.md), and
[runtime](native/SIMPLE_RUNTIME.md) describe the project. English translations
of the 18 historical contract files are in `history/contract-v1/`; original
Portuguese versions and removed implementations/captures remain in Git history.
