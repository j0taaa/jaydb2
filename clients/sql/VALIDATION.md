# SQL/Drizzle validation — 2026-11-06

The tested scope is the owner-isolated task schema, key-based CRUD, one/two-row
inserts, ordered projections up to 16 columns, defaults and `RETURNING` with
Drizzle 0.45.4. The supported scope remains in [README.md](README.md).

## Fixes established by regression tests

- SQL query calls now execute in invocation order across cached and uncached
  programs. A bounded queue retains fresh per-call credentials and arguments,
  and failures do not poison later work.
- Quoted identifiers and string tokens cannot masquerade as qualified `*`.
  Qualified write targets, malformed Unicode/NUL SQL, empty quoted identifiers,
  invalid whitespace and non-array parameters are rejected.
- Compiled metadata is frozen so callers cannot silently change later binding.
  The 16-column limit bounds generated terms before Bend generation.
- Success responses must have valid required cell types, row cardinalities and
  affected counts. Sparse arrays and malformed responses retain failure semantics.

## Frontend and independent reference checks

All 40 frontend tests passed on local Ubuntu/Node 24.19.0, cloud Ubuntu/Node
24.15.0 and a CentOS VPS/Node 24.14.0. The CentOS run tested the frontend only.
These include 6,144 grammar-generated valid CRUD queries, 1,024 independent
SQLite projection comparisons, 2,048 unsupported-suffix rejections, and 20,000
deterministic malformed-token fuzz inputs: 29,216 generated checks in total,
plus targeted regression and boundary assertions. They are not 29,216 native
database executions.

Concurrency tests execute 1,536 simulated requests across 128 distinct control
schedules. A diversity assertion prevents PRNG low-bit repetition from being
mistaken for independent scheduling coverage.

## Native SQL/Drizzle checks

All ten generated program shapes passed both official checking modes (20
checks): key SELECT, one/two-row INSERT, UPDATE and DELETE, each with ordinary
and maximum-width projections. The final 26-case integration run passed real admission, official
compilation, native execution, fresh authentication, owner isolation, duplicate
rollback, raw malformed arguments, wrong-table/wrong-owner proof rejection,
durable recovery and instance-local handle invalidation.

Three independent SQLite differential runs passed:

- Seeds `1,7,42`, 200 operations each: 600 randomized steps, 638 raw SQL and
  175 Drizzle comparisons, 176 expected duplicate refusals and 817 prepared SQL
  execution requests. [Raw result](validation/stress-600.json).
- Seeds `11,97,2026,3735928559`, 250 operations each: 1,000 randomized steps,
  988 raw SQL and 264 Drizzle comparisons, 255 expected duplicate refusals and
  1,256 prepared SQL execution requests. This stronger run also compares complete native
  and SQLite key sets for both actors before and after recovery, as well as
  all attempted keys' values/absences: four key-set audits and 48 recovered
  observations. [Raw result](validation/stress-1000.json).
- After concurrent admission/lifecycle changes were merged at `7e4bec4`, the
  complete SQL gate was repeated on that newer committed runtime in an Ubuntu
  24.04 container on the second VPS, using Node 24.14.0. Typechecking, all 40
  frontend tests, all 20 proof checks, all 26 integration checks and all 31
  boundary checks passed with individually recorded zero exit codes. Seeds
  `101,202,303`, 200 operations each, then passed 600 additional randomized
  steps: 661 raw SQL and 175 Drizzle comparisons, 180 expected duplicates,
  840 prepared SQL execution requests, four complete key-set audits and 48
  recovered observations. [Raw result](validation/stress-latest-600.json).

Together these runs cover 2,200 randomized operations across ten distinct seeds.

Validation reads and deterministic controls are included in the comparison and
execution counts; they must not be added again as independent randomized steps.
Key enumeration uses the separately certified task program, not an SQL scan.
The oracle executes original SQL in SQLite and uses its constraints, statement
rollback, defaults and retained state. It does not interpret the frontend AST.
Drizzle writes use its three-column writable metadata to stay within SQLite's
common syntax; owner/`DEFAULT` behavior is also exercised by the dedicated
Drizzle integration test.

## Full regression and size-limit gates

The dedicated SQL boundary gate passed all 31 checks. It executes 16-column
`RETURNING` for one/two-row INSERT, UPDATE and DELETE. It also checks a valid
20,000-byte field, 40,000-byte responses that exceed the response ceiling,
70,000-byte writes that exceed the state ceiling, a provisional first row
followed by an oversized second row, and 9,000 emoji whose 36,000 UTF-8 bytes
exceed the ceiling despite having fewer than 32,768 JavaScript code units.
Failed statements preserve exact durable snapshot bytes. Narrow projection
of a valid large row succeeds; oversized reads fail without deleting it, and
the next operation and durable reopen both succeed.

The isolated full release command passed frontend/host/accessory/starter checks,
all positive and negative proof aggregates, admission/verifier/native/service
checks, library checks (including 3,960 arithmetic/sort/summary/join/group cases
and 250 variable-length collection cases), and the indexed/combined host flows.
Its long SSH command ended with signal 143 during receipt validation, without a
test assertion failure. An independent remote supervisor then reran all feature
gates, including the complete receipt/restart flow, and completed all nine
storage-fault, process-death, timing and lost-response recovery tests and all
seven web-demo/transport tests. The resumed command exited zero. Thus all
release gates completed across the original and resumed commands; the original
full command itself did not exit zero. [Recorded gate results](validation/regression.json).

## Environment and reproduction

The broad native host is the user's Tailscale cloud machine running Ubuntu 24.04,
Node 24.15.0, Rust/Cargo 1.98.0, Clang 19.1.1, official Bend 2.0.39 and the
unchanged pinned BendTT artifact. It uses an immutable runtime source snapshot
from `441f807c24b1bbac32e6f08941b12622ce58d635` plus the SQL changes identified by
[source hashes](validation/source.sha256). It has a separate heavy-test lock.
The latest-runtime repeat uses the same pinned Bend/BendTT and Clang 19 in an
Ubuntu 24.04 container on the CentOS VPS, limited to two CPUs and 2 GiB RAM.
The runtime source revision is `7e4bec4`; this focused repeat verifies SQL
compatibility with the newer merged admission and lifecycle changes. The
broader release run remains explicitly tied to the earlier frozen revision.

The initial live-checkout full run reached admission tests but observed hash
mismatches while other work was editing the pinned read-only runtime/admission
files. The isolated rerun excludes those unrelated uncommitted edits. They were
neither reverted nor included in the SQL changes. Local logs are retained under
`build/sql-validation-20261106/`.

```sh
npm ci --prefix clients/typescript
npm ci --prefix clients/sql
make test-sql
(ulimit -s unlimited
 flock /tmp/jaydb2-experiments-heavy.lock make test-sql-native)
(ulimit -s unlimited
 SQL_STRESS_SEEDS=11,97,2026,3735928559 SQL_STRESS_STEPS=250 \
 SQL_STRESS_REPORT=build/sql-stress.json \
 flock /tmp/jaydb2-experiments-heavy.lock make test-sql-stress)
bash tools/ci/check.sh full
```

Testing supplies evidence for the documented subset. It does not establish
complete PostgreSQL equivalence, arbitrary-schema/law support, SQL compiler
correctness as a formal theorem, or hardware power-loss safety. The generated
certificates establish the existing JayDB law and termination obligations under
the documented service/toolchain assumptions. No database law was weakened.
