# SQL and Drizzle on JayDB2

This experimental frontend compiles a small PostgreSQL SQL subset to ordinary
Bend 2 programs and universal certificates. The existing service checks both
official proof modes, compiles the checked program and runs it on the normal
runtime. It uses the existing task application's ownership laws unchanged.

The first adapter exposes one logical table, `tasks`, backed by the table named
after the authenticated user. Alice and Bob can each insert `id = 't1'` without
sharing that row. SQL callers cannot choose the physical table or write an
owner. This is a policy-specific prototype, not PostgreSQL compatibility for
arbitrary schemas. Supporting another schema or policy requires another Bend
emitter and matching certificate construction.

## Try the real Drizzle example

Install the pinned database toolchain from [INSTALL](../../INSTALL.md), then:

```sh
make build
npm ci --prefix clients/sql
(ulimit -s unlimited; node clients/sql/examples/tasks.ts)
```

The example creates a disposable real database, inserts a task using Drizzle,
updates completion, selects the task and deletes it. It uses public demonstration
credentials. Python packages the existing Bend application at setup; SQL
compilation and client execution use TypeScript/Node. The frontend is a private
source package in this checkout; it is not published to npm.

```ts
import { eq, sql } from 'drizzle-orm';
import { boolean, pgTable, text } from 'drizzle-orm/pg-core';
import { Client } from '../typescript/src/index.ts';
import { SqlClient } from './src/index.ts';
import { createDrizzle } from './src/drizzle.ts';

const tasks = pgTable('tasks', {
  id: text('id').primaryKey(),
  title: text('title').notNull(),
  completed: boolean('completed').notNull().default(false),
  owner: text('owner').notNull().default(sql`current_user`),
});

// pipe is an existing Client connected to the packaged SQL task configuration.
const frontend = new SqlClient(pipe, { credential: () => currentCredential });
const db = createDrizzle(frontend);
await db.insert(tasks).values({ id: 't1', title: 'Try SQL' }).returning();
const rows = await db.select().from(tasks).where(eq(tasks.id, 't1'));
```

The Drizzle declaration describes the fixed logical schema. It does not execute
DDL. `owner DEFAULT` means the authenticated context ID in this adapter;
`completed DEFAULT` means false. Explicit owner values are rejected. The adapter
uses Drizzle 0.45.4's [PostgreSQL proxy callback](https://orm.drizzle.team/docs/connect-drizzle-proxy).
Query-builder CRUD is supported; relational-query APIs, migrations and
introspection are outside this prototype.

## SQL interface

```ts
const result = await frontend.query(
  'UPDATE tasks SET title = $1 WHERE id = $2 RETURNING id, title',
  ['A new title', 't1'],
);
// { columns: ['id', 'title'], rows: [['t1', 'A new title']], rowCount: 1n }
```

| Supported | Behavior |
| --- | --- |
| `SELECT columns FROM tasks WHERE id = value` | Key lookup; a missing row returns no rows. |
| `INSERT INTO tasks (columns) VALUES (...) [, (...)]` | One or two rows, atomically; duplicate keys refuse the entire statement. |
| `UPDATE tasks SET title = value, completed = value WHERE id = value` | Either or both assignments; unspecified fields retained; missing row affects zero rows. |
| `DELETE FROM tasks WHERE id = value` | Missing row affects zero rows. |
| `RETURNING columns` | Insert/update return new values; delete returns old values. |
| Projections | `*`, column aliases, qualified column names, duplicate columns, positional result order. |
| Values | `$1` parameters, SQL string and boolean literals, insert defaults. |

Every statement produces one ordinary atomic JayDB transaction. Multi-row
inserts perform their existence checks and writes inside that transaction;
there is no client-side read-before-write or partial commit. Duplicate keys
produce `SqlExecutionError` with SQLSTATE `23505`. Other non-success database
statuses throw errors retaining the original response; they never become empty
successful results. Transport errors retain the client's unknown-outcome
meaning and writes are never retried automatically.

The logical columns are required text `id`, required text `title`, boolean
`completed` (default false) and required text `owner` (default authenticated ID).
Key predicates require text. `NULL`, casts, numeric coercions, expressions,
arithmetic, scans, joins, aggregates, ordering, pagination, `ON CONFLICT`, DDL,
migrations and multiple statements are rejected explicitly. `id` and `owner`
updates are unsupported. In particular, `WHERE id = NULL` is rejected rather
than implementing SQL's null logic. Parentheses are bounded to 64 levels and
SQL source to 64 KiB and projected output to 16 columns by the frontend.

## Compilation and proof boundary

`compileSql(sql)` returns `{ code, proof, statement, columns, bind }` for inspection.
Statement metadata and output labels are frozen so inspection cannot change
the binding behavior of an already compiled program.
The compiler emits a program specialized to the statement's operation,
projection and insert row count. Literal and bound values become execution
arguments; SQL values never enter generated Bend source. `bind(params)` checks
types before any registration or execution. SQL is tokenized and parsed with
complete consumption, including quoted strings and comments.

`SqlClient` prepares each generated source shape once per session and uses the
existing prepared-handle protocol afterward. Query calls execute in invocation
order, including when an earlier query needs preparation and a later query's
program is already cached. Credentials and arguments are captured at invocation.
Failed queries do not poison later queued work. Registrations may be
shared across credentials. Every execution submits the captured
credential and authenticates against current published state. Handles do not
grant identity. The default local cache is bounded to 64 source shapes; a full
cache reports an error. The local queue is bounded to 64 outstanding queries,
configurable through `maxPendingQueries`; excess queries are rejected before
submission. Use one SQL client per pipe session. There is no
automatic invalidation, reprepare or reconnect; restart requires a fresh client.
Await query promises before closing the underlying pipe so its shutdown can
follow all work queued by the SQL frontend.

The generated safety proof covers the actual program's accesses, all execution
prefixes, ownership preservation and termination. No administrator law is
relaxed. Key SELECT/UPDATE/DELETE currently read both `title` and `completed`,
even when the projection contains only `id`; this is authorized by the existing
task ownership policy. Those reads must be considered when adding other policies.

The certificates establish compliance with JayDB's laws, not a formal theorem
that the translator implements SQL. SQL behavior is validated by parser,
binding, Drizzle and real-service tests. Parsing, source generation, result
mapping and the existing trusted service/toolchain boundaries retain their
ordinary implementation assumptions. This feature adds no network listener or
PostgreSQL wire protocol.

## Verification

```sh
make test-sql
(ulimit -s unlimited
 flock /tmp/jaydb2-experiments-heavy.lock make test-sql-native)
(ulimit -s unlimited
 flock /tmp/jaydb2-experiments-heavy.lock make test-sql-stress)
```

The fast checks cover actual Drizzle-generated SQL, unsupported-feature errors,
type/default validation, hostile text, positional mapping, concurrent
authentication and cache behavior. The native target checks generated SELECT,
SELECT at the 16-column projection limit, INSERT (one and two rows), UPDATE
and DELETE certificates with both
official checking modes, then executes actual Drizzle/SQL against the service.
It checks atomic duplicate rollback, owner isolation, fresh authentication,
wrong-table/wrong-owner proof rejection, malformed raw arguments, and durable
close/reopen. Its size-limit gate checks large fields, byte-counted UTF-8
responses, state limits, provisional-write rollback and recovery after limits.
These checks are included in smoke/full validation respectively.
`JAYDB_SQL_BINARY` can select an equivalent service built from a frozen runtime
source snapshot when other work is editing this checkout. Recovery requires
unchanged runtime source bytes as well as the same executable.

The stress target executes 600 reproducible randomized operations by default,
mixing raw SQL and real Drizzle calls against an independent SQLite oracle. It
also checks duplicate rollback, concurrent invocation order, fresh credentials,
Unicode/control text, named Drizzle preparations, full retained state and
durable recovery. It executes original SQL in SQLite; it does not interpret
the frontend AST as its reference. SQLite is an oracle for the common supported
subset, not proof of PostgreSQL equivalence. Override `SQL_STRESS_SEEDS` (comma
separated uint32 values), `SQL_STRESS_STEPS` (per seed), and
`SQL_STRESS_REPORT` (JSON output path) for longer reproducible runs.

The pinned official secondary checker overflows its stack on larger expanded
INSERT certificates, so this prototype caps INSERT at two rows. Supporting
larger batches requires a different certificate construction or toolchain work.

The SQL fixture raises only the message ceiling to 131072 bytes to accommodate
the generated multi-row source and proof. State and response limits remain
65536 and 32768 bytes. Parameters and returned data still obey those limits.
