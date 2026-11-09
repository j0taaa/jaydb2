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

GPU execution is available on this experimental integration branch. Use
`--gpu 512` to opt into official CUDA execution for explicit `!` calls,
with a 512 MiB corpus. CPU remains the default (`--gpu off`); initialization
and authentication always use CPU. See [GPU scope and requirements](experiments/gpu/REPORT.md).

## Existing database capabilities

Requests are FIFO and serial by default. The host bounds queued work and applies
pipe backpressure. Each call uses fresh native workers emitted by the official
compiler; the host retains the last published state.

- **[Prepared programs](tools/service/PREPARED_PROGRAMS.md):** check and compile
  a universally certified program once, then execute its instance-local handle
  with fresh credentials and arguments. Restart loses handles.
- **[Complete-image persistence](experiments/persistence/REPORT.md):** opt-in
  `--storage DIRECTORY --storage-mode create|open`. Open reads no seed and
  requires the exact executable/environment. Development databases can be
  recreated after changes; cross-build compatibility and migrations are outside
  scope. Uncertain commit failures stop service rather than promise rollback.
- **[Certified CPU read batches](tools/service/READ_BATCHES.md):** optional
  `--threads 4 --read-workers 2`; only separately certified whole-program reads
  overlap. Writes and prepared controls remain FIFO barriers. One reader is
  the default. `--threads N` selects a total native-worker budget of 1–128.
- **[Administrator timing](tools/service/SERVICE_TIMING.md):** opt-in
  `--timing-log FILE` (or `-` for stderr), through cleanup and publication.
  Queue waiting and response delivery are excluded. Client bytes are unchanged.

This experimental branch additionally supports opt-in GPU execution. The Bend
host replacement and quota enforcement remain excluded.
The database contract has three canonical size limits: message, state and
response. There is no total-process memory guarantee or custom per-stage
deadline. A fatal failure can terminate an instance; volatile data is then lost.

## Branches

`main` contains the accepted CPU capabilities, optional SQL/Drizzle frontend,
database comparison suite and TCC sources. SQL/Drizzle is an application layer;
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

The [main-merge review](experiments/integration/MAIN_REVIEW.md) records the
reviewed engine, concrete repairs and raw validation evidence. Experiment
reports retain their historical revisions and measured scope.

The subsequent [project review](docs/review.md) records further repairs,
proof coverage and remaining obligations. The English
[TCC article and editable defense slides](paper/README.md) use the project's
verified evidence and identify its trusted boundaries.

## Guarantees and assumptions

The [specification](SPECIFICATION.md), [Bend contract](contract/README.md),
[service](tools/service/SIMPLE_SERVICE.md), and [runtime](native/SIMPLE_RUNTIME.md)
define behavior and official-tool limitations. The source proofs cover the
kernel and declared service models under the explicit
[integration contracts](proof/SERVICE_CONTRACT.md). Rust/Node/C, Clang, the OS,
storage assumptions and official translations remain trusted boundaries;
review and tests do not constitute a mechanized proof of those components.

JayDB2 does not modify the official frontend, checker, compiler, runtime, or
emitted C. Source and executable hashes are pinned in
[toolchain.lock.json](tools/admission/toolchain.lock.json). Authentication uses
current published state; configuration and dependencies are public and immutable,
while seed/current state remain private. Public names and protocol fields are
English-only, with no legacy aliases.
