# Ten realistic databases: JayDB2, PostgreSQL, and SQLite

**Run status: results pending.** The final measurement run is writing to
`build/database-comparison-final/result.json`. Replace the result placeholders
below only after the run has finished, its source checks have passed, and all
30 engine/scenario records have been reviewed. The methodology and inspected
capabilities below describe the frozen suite used by that run.

This experiment asks whether the same application data can be created, accessed,
changed, checked, and reopened in three real engines. It separates three questions:
whether a schema and its sample data can be represented; whether the database
enforces the application's relationships; and what the implemented workflows cost.
A successful import alone does not establish production application feasibility.

## Results to complete after the measured run

<!-- RESULTS_SUMMARY_START: replace this block after final result.json passes. -->

- Engine/scenario completion: **[PENDING: passed/failed counts and specific failures]**.
- Data and transaction checks: **[PENDING: equivalence, type errors, rollback,
  duplicate IDs, foreign keys, and reopen/restart outcomes]**.
- Point operations and setup: **[PENDING: per-project medians and setup totals]**.
- Aggregation and relationships: **[PENDING: per-project medians, labeled as
  native SQL versus the implemented multi-call Jay workflows]**.
- Storage and observed memory: **[PENDING: values with the scope qualifications
  below attached]**.
- Practical interpretation: **[PENDING: conclusions supported by completed runs;
  distinguish representation success from missing enforced invariants]**.

<!-- RESULTS_SUMMARY_END -->

## Projects and data

Three agents created the simple, medium, and complex projects concurrently. The
projects use business entities and relationships rather than copies of one
generic key/value table. Execution is serialized so simultaneous agent work does
not become simultaneous benchmark load.

| Project | Application tables | Application rows | Declared references | Representative work |
| --- | ---: | ---: | ---: | --- |
| [Personal task planner](scenarios/01_personal_tasks.json) | 1 | 8 | 0 | Revise effort estimates and total planned minutes |
| [Household budget](scenarios/02_household_budget.json) | 3 | 24 | 2 | Correct ledger amounts and attach spending categories |
| [Editorial publishing](scenarios/03_editorial_blog.json) | 5 | 40 | 5 | Update reading time and attach article authors |
| [Coffee ecommerce](scenarios/04_ecommerce.json) | 8 | 64 | 7 | Change inventory and resolve order-line products |
| [Outpatient clinic](scenarios/05_clinic.json) | 10 | 80 | 9 | Change invoice amounts and resolve related records |
| [Learning platform](scenarios/06_learning_platform.json) | 12 | 96 | 14 | Change grades and resolve learning relationships |
| [Hotel operations](scenarios/07_hotel.json) | 15 | 120 | 18 | Change payments and resolve stay-related records |
| [Contract logistics](scenarios/08_logistics.json) | 18 | 144 | 26 | Change shipment invoice lines and resolve customers |
| [Manufacturing](scenarios/09_manufacturing.json) | 22 | 176 | 29 | Change sales-order pricing and resolve products |
| [Municipal services](scenarios/10_municipal_services.json) | 26 | 208 | 40 | Change expenditures and resolve administrative records |
| **One complete engine catalog** | **120** | **960** | **150** | |

There are eight rows per table. These fixtures span increasing schema breadth,
not large row counts: even the largest project contains only 208 application
rows. Table count, total state size, field widths, target-table position, and
relationship layout change together. A trend across projects cannot isolate any
one of those variables or establish a database size limit.

Every table has a text primary key and three to six required scalar columns.
Dates use ISO strings, money uses integer minor units, and booleans retain Boolean
meaning. The portable model does not use nullable columns, floating point,
native timestamps, decimal arithmetic, generated IDs, or vendor-specific types.
Each scenario describes its business workflow and modeling limitations. A clinic
fixture is synthetic scheduling/billing data; it is not a validated medical
records system. Similarly, the budget is a cash-flow ledger rather than a
double-entry accounting implementation.

The mutation workload deliberately writes synthetic integers based on
`10000 + iteration`, with additional offsets for the two-row transaction. These
can exceed realistic bounds for grades or article reading minutes. Neither
fixture declares those business range invariants. The seeds are realistic; the
timed mutations assess technical CRUD and transaction behavior, not continued
validity of every business workflow.

## What actually runs

JayDB2 runs the freshly built release controller with the pinned official Bend
2.0.39 toolchain. Each project has a real generated configuration and a checked
empty seed, then receives every application row through admitted prepared
writes. Three reusable programs provide single operations, a two-write
transaction, and a six-cell row read used for complete validation. Their
certificates and finite termination witnesses go through normal preparation.
The benchmark does not replace the engine with a Python model.

Jay uses `Free.configuration`: **zero administrator business or permission laws
are installed**. Authentication, schema/type checks, technical limits,
certificate admission, termination checking, artifact integrity, native workers,
and publication remain enabled. This is a permissive typed database experiment;
the certificates do not establish foreign keys, money conservation, ownership,
inventory rules, or the functional correctness of the Python workflows.
The configuration allows 256 KiB messages, 8 MiB canonical state, and 256 KiB
responses; these are logical size limits, not a total-process memory bound.

PostgreSQL has one actual `cmp_<scenario>` database per project in an isolated
local cluster. It uses a private Unix socket, no TCP listener, 32 MiB
`shared_buffers`, and `fsync`, `synchronous_commit`, and `full_page_writes` enabled.
The driver runs in autocommit mode and enables server preparation immediately.
SQLite has one real `database.sqlite` per project, with `STRICT` tables,
`foreign_keys=ON`, WAL journaling, and `synchronous=FULL`. Both SQL engines declare
all references, required columns, and text primary keys. SQLite stores booleans
as checked integers and the adapter converts query results back to Python bools.

These settings matter. SQLite `STRICT` rejects values that cannot be converted
to the declared type, but still permits lossless coercion; it is not identical
to Jay's no-coercion value semantics. The suite tests a nonnumeric string in an
integer field, not every conversion boundary. SQLite foreign-key enforcement
must be enabled per connection, which the adapter does on creation and reopen.
See the primary [SQLite STRICT](https://www.sqlite.org/stricttables.html) and
[foreign-key documentation](https://www.sqlite.org/foreignkeys.html).

## Measurement and correctness

The final run uses Python 3.11.16, SQLite 3.53.1, PostgreSQL 16.15, and Node
24.19.0 on Linux x86-64, an Intel Core i7-11700K, 16 logical CPUs, and approximately
15.5 GiB RAM. The raw manifest records exact versions, available affinity, initial
and final load, source identities, and binary hashes. Jay uses one native worker
and the default single-reader path. PostgreSQL retains its normal background
processes; an embedded SQLite call runs in the client process. These are the
actual deployment paths, not an equal process-count or equal CPU-affinity trial.

Only one engine/scenario is measured at a time under the repository's shared
heavy-work lock. Engine order rotates between scenarios. Each workload has one
warmup and seven recorded samples; workload types alternate within each
iteration. Samples reuse the open instance and OS caches. This is a warm local
single-client comparison. The shared lock coordinates participating repository
experiments, not all activity on the computer.

| Workload | Logical result | Jay implementation | SQL implementation |
| --- | --- | --- | --- |
| Point read | One integer cell by existing key | One prepared service call | One parameterized `SELECT` |
| Point update | Replace one integer cell | One prepared service call | One committed `UPDATE` |
| Two-row transaction | Change two rows atomically | Two accesses in one prepared program | Two updates within `BEGIN`/`COMMIT` |
| Scan sum | Sum eight integer values | Enumerate keys, then eight independent cell calls | One native `SUM` query |
| Relationship join | Ordered child ID/parent-value pairs | Enumerate child keys, then two cell calls per child | One native `JOIN` query |

The one-table task project has no relationship join. For all other projects,
the join resolves one declared child-to-parent reference; it does not join every
table of the schema. Each sum scans one eight-row table. The large schemas
therefore test the effects of surrounding state and schema breadth on small
operations, rather than a complex reporting query over all their entities.

Timers cover the Python adapter call through its decoded result, including
encoding, transport, and decoding where applicable. This makes the results
useful for these client workflows, but includes pipe and fresh-worker overhead
for Jay, Unix-socket/driver overhead for PostgreSQL, and an in-process call for
SQLite. Expected-value calculation and validation reads occur outside each timed
sample. Validation still changes cache warmth and, for default durable Jay reads,
performs publication work between samples.

Setup is measured separately as database/schema/client creation and population.
Jay setup includes generation, service initialization, checking and compilation
of all three prepared programs. SQL setup includes its database or file, DDL,
connection, and adapter initialization. Shared Rust compilation is recorded
separately; existing Jay toolchain provisioning, dependency installation, and
PostgreSQL cluster creation are not part of each database's setup timing.
SQL schema creation commits each `CREATE TABLE` separately in this adapter;
its setup timings could improve by grouping DDL into a transaction.

The oracle is an independent deep copy of the JSON business rows. Every initial
field is read back and compared, and each timed result is checked. Warmups and
samples both update the oracle. Each changed cell is independently queried after
its timed write. Additional real-engine probes check:

1. A missing row returns no value.
2. A nonnumeric string cannot replace an integer, and the old cell remains.
3. If the second write in a two-write transaction fails, the first write is also
   absent from published data.
4. Reusing an existing ID reveals replacement versus strict insertion behavior;
   the original row is restored afterward.
5. Changing a reference to a missing parent reveals whether that relationship is
   enforced; any accepted orphan is restored afterward.
6. Inserting, reading, deleting, and rereading a new leaf-table row completes a
   CRUD roundtrip.
7. Reopen is followed by a full comparison of every final field, not a single
   sentinel read. PostgreSQL additionally receives a complete cluster restart
   and full-data verification at the end of the catalog run.

Result comparisons use Python structural equality, which treats Boolean and
integer equivalents such as `True` and `1` as equal. The adapters normalize SQL
booleans, but these full-data comparisons do not independently establish exact
primitive wire-type fidelity. The wrong-type probe specifically checks rejection
of a nonnumeric string in an integer column.

These probes distinguish correct implementation of the configured semantics
from stronger semantics that were never configured. Jay's `DefineRow` is an
insert-or-replace operation; this suite's SQL adapter deliberately uses strict
`INSERT`. Jay can implement insert-if-absent, but that requires an existence
check and certified composition. A rejected SQL duplicate and a successful Jay
replacement are therefore recorded behaviors rather than the same test outcome.
The semantics and helper are documented in
[the specification](../../SPECIFICATION.md) and
[the mutation helper contract](../../library/README.md#access-and-transaction-contracts).

Medians, minima, maxima, median absolute deviations, individual samples, and
nearest-rank p95 are retained. With seven samples, p95 is the maximum observed
sample, not an estimate of a production tail distribution. The recorded
`serial_ops_per_second` is one billion divided by mean latency in nanoseconds.
It is a derived serial call rate, not measured concurrent or sustained throughput.

## Why aggregation and durable reads need separate interpretation

The Jay sum makes nine service requests; its eight-row join makes seventeen.
SQL returns each result in one request. That difference is an implementation
choice with a real simplicity and performance cost in this suite. It does not
show that Jay cannot aggregate or join inside a single certified program.
The existing [library](../../library/README.md#extended-ordinary-library)
provides `Aggregate`, `Relation`, access traversal, and query helpers. They
operate on values obtained through explicit accesses and retain the caller's
permission and termination obligations. Producing and proving an efficient
single-call relational program is additional application work that this suite
has not done.

There is also a persistence multiplier: Jay's default serial durable path writes
and synchronizes a complete snapshot for every successful state proposal,
including an unchanged read. Consequently each of those nine or seventeen calls
can repeat full-image publication. Prepared execution removes repeated compiler
and checker invocation; it retains fresh authentication/execution processes,
integrity checking, and publication. This follows the current
[service persistence contract](../../tools/service/SIMPLE_SERVICE.md#ownership-and-failures)
and [prepared execution contract](../../tools/service/PREPARED_PROGRAMS.md).

Jay has a separately certified read-batch path that can avoid rewriting an
already durable snapshot. This suite uses neither that path nor a read-only
certificate, and does not measure the alternative. It would require a separate
controlled experiment. SQL's WAL and MVCC paths are also different persistence
designs, so enabling durable settings on all engines does not equate their I/O
work. SQLite's [WAL documentation](https://www.sqlite.org/wal.html) describes
commits into a log and subsequent checkpointing.

## Capability and access comparison

The following are inspected capabilities, not new benchmark results, unless a
specific runtime probe is named. SQL features outside the portable schema and
workloads were not exhaustively exercised.

| Area | JayDB2 | PostgreSQL | SQLite |
| --- | --- | --- | --- |
| Stored scalar model | Unicode text, bool, signed64 integer, optional explicit absence; one mandatory text key | This suite uses text, bigint, Boolean, and required text keys | This suite uses STRICT text/integer columns, checked booleans, required text keys |
| Relationships | No implicit kernel FK; administrator laws can require references | Declared `REFERENCES` in this suite | Declared `REFERENCES`, enabled on every connection |
| Query access | Source and proof, optionally prepared once; explicit internal accesses | Parameterized SQL through psycopg | Parameterized SQL through the standard library |
| Indexes | Reference lookup traverses lists; optional derived index tables need explicit maintenance/laws | Primary keys have automatically created unique indexes | Text primary-key constraints and native SQL indexes; no additional benchmark indexes |
| Schema evolution | Configuration is fixed; current durable profile requires the exact environment and excludes migrations | `ALTER TABLE` supports schema changes | `ALTER TABLE` supports a subset of changes; other changes may need reconstruction |
| Authentication in this run | Current published credential checked per request; permissive application laws | Local trusted connection to private socket; no password or role-policy benchmark | File/process access; no separate database server login in this adapter |
| Concurrency inspected | Serial default; optional certified CPU read batches, with writes and controls as barriers | MVCC supports concurrent sessions | WAL permits readers alongside a writer; writes serialize |
| Persistence exercised | Complete image, clean service stop/open, handles prepared again | Committed transactions, client reconnect, then whole-cluster stop/start | FULL WAL commits and connection/file close/open |

Jay's type/key restrictions and lack of implicit relationships follow
[SPECIFICATION.md](../../SPECIFICATION.md), especially the responsibilities and
common-definition sections. The actual list traversal is in
[contract/Data.bend](../../contract/Data.bend), `find_row`, `find_schema`, and
`find_table`. Derived indexes and reference-law templates appear in
[library/README.md](../../library/README.md); ordered/range indexing, full text,
geospatial access, and a query optimizer are outside its stated scope.

PostgreSQL's primary-key index behavior and schema changes are documented in
[unique indexes](https://www.postgresql.org/docs/16/indexes-unique.html) and
[modifying tables](https://www.postgresql.org/docs/16/ddl-alter.html).
SQLite's alteration options and reconstruction procedure are described in
[ALTER TABLE](https://www.sqlite.org/lang_altertable.html). None of these migration
or index-design alternatives was benchmarked here.

The concurrency row follows
[Jay's read-batch contract](../../tools/service/READ_BATCHES.md),
[PostgreSQL MVCC](https://www.postgresql.org/docs/16/mvcc-intro.html), and
[SQLite isolation](https://www.sqlite.org/isolation.html). There are no competing
clients in this run, so it provides no evidence about contention, fairness,
write concurrency, or multiuser throughput.

Authentication is likewise not normalized. PostgreSQL offers several methods,
but this isolated cluster uses trust at connection establishment; see
[PostgreSQL authentication](https://www.postgresql.org/docs/16/auth-methods.html).
Jay performs its own fresh per-request authentication while SQLite relies on
the hosting process and file access. These timings cannot compare equivalent
security configurations or the value of restrictive verified policies.

## Setup and developer effort

The scenario JSON is the shared modeling work. It drives generated DDL in SQL
and generated schema/seed sources in Jay. This demonstrates that automation can
reduce repeated schema typing; it does not mean arbitrary relational business
constraints were automatically translated into Jay laws.

Concrete source artifacts expose the extra work. The frozen Jay adapter is
222 lines and its three Bend programs total 102 lines, with universal proof and
seed-proof templates included in the adapter. The shared dual-engine SQL
adapter is 202 lines. These counts include blank lines and comments and are not
normalized measures of language complexity, feature completeness, or development
time. No invented person-hours or subjective numeric usability scores are used.

The material differences are visible in the workflow: SQL clients bind values
and send SQL after opening a connection. Jay clients first need a schema/seed,
an admitted source/proof pair, and prepared handles; a service restart loses the
handles. The supplied generic programs amortize that work across all ten
schemas. Restrictive ownership or reference policies would introduce additional
proof design beyond this experiment. SQL schema constraints also leave many
business rules unspecified, so its successful imports do not validate complete
business applications either.

For local access, SQLite needs no dedicated service in this implementation.
PostgreSQL needs a server/cluster and a driver. Jay needs the controller, pinned
Bend toolchain, Node, Clang, public sources, and application proofs during
initialization/preparation. The installation and operational requirements are
concrete access costs, even when not part of steady-state latency.

## Storage, memory, and restart scope

Storage is reported with its accounting scope attached:

- Jay counts files in its `storage/` directory. Prepared native executables,
  compilation products, source/toolchain files, and logs are outside that count.
- PostgreSQL uses `pg_database_size` for the scenario database. It includes the
  per-database catalog/index baseline; shared cluster files and WAL are outside
  that value. A catalog-heavy small database is not a measure of marginal row
  storage density.
- SQLite live size includes its database, WAL, and shared-memory sidecar files;
  closed size is measured separately after connection shutdown. Checkpointing
  and sidecar allocation affect the difference.

Observed memory is sampled every 10 ms during the workload loop. Jay's scope is
its controller and descendants. PostgreSQL's scope is the entire private
cluster, including background processes and any retained cache from earlier
projects. SQLite's scope is the Python harness containing the embedded engine,
adapter, interpreter, oracle, and accumulated result records. Summed RSS counts
shared resident pages once per process and sampling can miss short-lived peaks.
It is neither PSS nor database-only allocation, and these scopes do not support
a clean cross-engine memory-efficiency ranking. Setup/compilation peaks are
outside the sampling window. See [memory.py](memory.py) for the exact sampler.

The per-project reopen timing is asymmetric by design and must retain its name:
Jay stops the service, opens the durable database, and prepares all three handles
again; PostgreSQL reconnects the client to its running server; SQLite closes and
reopens its connection/file. The final PostgreSQL whole-cluster restart is
recorded separately, once for all its projects, and every successful project's
final data is checked afterward. These are clean stop/start checks, not killed
process, corrupt image, disk-full, OS crash, or power-loss experiments. Successful
reopening is a tested operational property, not a proof of power-failure safety.

## Evidence and reproducibility

The canonical local run directory is
`build/database-comparison-final/`. Its root `result.json` contains individual
samples, summaries, correctness outcomes, hardware/tool versions, dirty Git
status, source and suite SHA-256 maps, scenario hashes, pinned Bend toolchain
identities, and the freshly built Jay executable hash. The measured Git head is
`0552c768811d0c05af07fcf5d02fbec03e245db2`; this experiment and preexisting local
work were also present, so a clean revision alone does not describe the run.
The retained patch and suite copy document that distinction.

Each engine/scenario folder retains its own `result.json`, generated schema or
configuration, final data, and diagnostic logs as applicable. Jay additionally
retains actual programs/proofs and durable storage; SQLite retains the actual
database file. A PostgreSQL SQL dump is produced after the cluster restart.
Production source identities and suite sources are checked for changes after
the measurement. Editing report Markdown does not change the frozen inputs.

**[PENDING: insert links to the compact committed evidence, final chart, and
reproduction README, and confirm the successful end-of-run identity checks.]**

Reproduction must use a new output directory and the documented local
PostgreSQL/driver environment; `run.sh` takes the shared heavy-work lock.
Full-field comparisons and source checks make correctness failures visible and
cause a failed run status. Failed or partial records must not be pooled into a
passing performance comparison.

Finally, the project explicitly treats the Rust/Node/C bridge, compiler/runtime,
OS, and storage assumptions as trusted boundaries. These benchmark checks add
concrete execution evidence; they do not mechanically prove those components or
extend the scope of the existing source proofs. See
[the service verification boundary](../../tools/service/SIMPLE_SERVICE.md#verification).
