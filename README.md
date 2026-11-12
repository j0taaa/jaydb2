# JayDB2

An experimental database that runs Bend programs accompanied by proofs against
administrator-defined laws. Every request authenticates against published state,
executes on a private proposal, and publishes only an accepted complete result.

Start with **[your first durable TypeScript application](QUICKSTART.md)**.
It saves a task, exits, reopens the database, and demonstrates isolation and
refusal rollback using the real service and existing application certificate.

## Install and try it

The supported execution profile is Linux x86-64, Node 24, Clang 19, Rust/Cargo,
and an unlimited hard stack limit. [INSTALL.md](INSTALL.md) installs the pinned
official Bend 2.0.39 and BendTT locally. Python 3.12 is used by development tools
and example clients; the server is Rust + Node + ordinary native executables.

After installation:

```sh
make build
node applications/tasks/tasks.ts \
  --workspace .build/tasks/first --storage-mode create \
  --command save t1 "Try JayDB2"
node applications/tasks/tasks.ts \
  --workspace .build/tasks/first --storage-mode open --command view t1
```

Use a fresh workspace for create. These examples have public demo credentials;
they are not a provisioned production account system.

For a disposable five-response credential/rollback session, use `make demo`.
For the local browser workbench, run `make demo-web` and open
http://localhost:8094. It uses a real database per session and supports editing
programs/proofs and administrator inspection. Its sessions remain volatile.
See [the web demo](demo/README.md) for its interface and limits.

## Build an application

- **[Experimental SQL and Drizzle](clients/sql/README.md):** PostgreSQL-subset
  key-based task CRUD compiled to ordinary Bend programs and universal proofs,
  with a real Drizzle proxy adapter. Uses the existing ownership laws.
- **[TypeScript client](clients/typescript/README.md):** optional Node library
  for binary framing, ordinary requests and prepared handles. Runtime dependencies
  are zero; int64 values use `bigint`. It never silently retries a write.
- **[Programs and proofs](docs/programs-and-proofs.md):** copyable CRUD and
  conditional-operation starters with working certificates, actual permission
  obligations and both-checker validation. No database extension is required.
- **[Optional Bend helpers](library/README.md):** values, records, keys,
  arithmetic, queries, conditional writes, relationships, ordinary-table index
  maintenance and receipts. Helpers retain their actual reads and application
  permission requirements; using the library is optional.
- **[Persistent tasks](applications/tasks/README.md):** a small Node/TypeScript
  application and interactive Python client using the same Bend program/proof.
- **[Receipt application](applications/vouchers/README.md):** application-level
  idempotency with exact inputs, current permissions and ordinary tables/laws.

The service uses stdin/stdout rather than a network listener. TypeScript web
applications can host the client in their Node backend; the client does not
expose the database directly to a browser or add a network security policy.

## Existing database capabilities

Requests are FIFO and serial by default. The host bounds queued work and applies
pipe backpressure. Each call uses single-use native workers emitted by the official
compiler; up to eight images process-wide, including the authenticator, keep
one data-free idle child ahead of selection. Further registrations spawn fresh. Verified sealed memfds preserve admitted executable bytes.
The host retains the last published state; see [native execution](native/SIMPLE_RUNTIME.md).

- **[Prepared programs](tools/service/PREPARED_PROGRAMS.md):** check and compile
  a universally certified program once, then execute its instance-local handle
  with fresh credentials and arguments. Restart loses handles.
- **[Complete-state persistence](tools/service/SIMPLE_SERVICE.md):** opt-in
  `--storage DIRECTORY --storage-mode create|open`. Open reads no seed and
  compares an immutable descriptor of the exact executable/environment bytes.
  Changed states normally overwrite an initialized alternate slot and call
  `fdatasync` once; growth uses safe image replacement. See the [storage protocol](docs/durable-storage.md).
  Development databases can be
  recreated after changes; cross-build compatibility and migrations are outside
  scope. Uncertain commit failures stop service rather than promise rollback.
- **[Administrator timing](tools/service/SERVICE_TIMING.md):** opt-in
  `--timing-log FILE` (or `-` for stderr), through cleanup and publication.
  Queue waiting and response delivery are excluded. Client bytes are unchanged.

Requests are processed serially. `--threads N` selects 1–128 native CPU workers
per process.

These capabilities do not add GPU execution, a Bend host replacement or quotas.
The database contract has three canonical size limits: message, state and
response. There is no total-process memory guarantee or custom per-stage
deadline. A fatal failure can terminate an instance; volatile data is then lost.

## Branches

`main` contains the accepted CPU capabilities, optional SQL/Drizzle frontend
and TCC sources. SQL/Drizzle is an application layer;
it does not replace the engine or change its core laws.

[`experiment-integration`](https://github.com/j0taaa/jaydb2/tree/experiment-integration)
is the combined experimental branch. It follows main and adds opt-in GPU
execution. New GPU work stays there and on `experiment-gpu` until separately
accepted for main. The Bend controller replacement remains isolated on
`experiment-bend-host`; quota enforcement remains excluded from integration.

## Checks

```sh
npm ci --prefix clients/typescript
npm ci --prefix clients/sql
make smoke
# Complete proof/native checks also need Clang 19 and unlimited hard stack:
make check-release
```

[Verification](docs/verification.md) describes the fast smoke gate and complete
proof/native/recovery/application checks, locally and in GitHub Actions. Smoke
alone does not establish proof or durability correctness. The older individual
`make verify-contract`, `make verify`, `make test` and application targets remain
available.

The English [TCC article and editable defense slides](paper/README.md) use the project's
verified evidence and identify its trusted boundaries.

## Guarantees and assumptions

The [executable contract](contract/README.md) has checked witnesses for
initialization, authenticated admission, every-prefix law safety, exact
finalization/publication, accepted execution progress, direct/registered
ingress, prepared-control transitions, mixed serial runs and canonical wire
encodings. `StartupTheorem` covers the executed initializer/recovery check;
T1 admits the exact seed-validity declaration before initialization runs. The
[proof guide](proof/README.md) gives precise premises, non-vacuity evidence and
the trusted base: T1 admission soundness and exact source/Book binding,
T2 compiler/runtime preservation, and T3 numbered host plumbing obligations.

The native worker executes the checked `Gate`/interpreter/finalizer path;
compiler/runtime preservation and physical host plumbing remain T2/T3.

Authentication uses current published state; configuration and dependencies
remain immutable. Scoped cached universal prepared admission specializes at
lookup for the current context and arguments under T1. Durability of
persistence, OS failures, resource availability and checker completeness or
adequacy are outside the proved guarantees. Rust/Node/C and physical IO remain
trusted integration components supported by tests.

Official Bend/BendTT tool sources and executable hashes are pinned in
[toolchain.lock.json](tools/admission/toolchain.lock.json). JayDB2 uses the
official frontend, checker, compiler, runtime and emitted C unchanged.
