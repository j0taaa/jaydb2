# Ten application databases, three real engines

This suite creates the same ten deterministic application datasets in real
JayDB2 storage instances, SQLite database files, and separate PostgreSQL
databases. The ten [projects](projects/) have 1, 3, 5, 8, 10, 12, 15, 18, 22,
and 26 tables, respectively, with eight realistic synthetic rows per table.
The [scenario JSON files](scenarios/) are the single source of schema, seed
data, query inputs, and domain caveats. All money uses integer minor units;
dates and domain enums are text. These are feasibility-sized datasets.

Read [REPORT.md](REPORT.md) for results, interpretation, and important differences
in integrity semantics and query execution. Each project contains actual Bend
configurations, programs and certificates, and executable SQLite/PostgreSQL DDL.
No mock database or SQL emulation is used.

From the repository root, first install the existing pinned JayDB2 toolchain
using [INSTALL.md](../../INSTALL.md). On Ubuntu 24.04 x86-64, optional comparison
dependencies can be extracted locally without root or a system service:

```sh
experiments/database-comparison/setup.sh
```

The script needs `apt-get`, `dpkg-deb`, and `uv`; it pins PostgreSQL 16.15 and
psycopg 3.2.13. If archived Ubuntu package versions disappear, supply an existing
Debian/Ubuntu-layout PostgreSQL 16 installation with `--pg-bin /path/to/bin`
and document its version. The cluster helper currently derives its library and
shared-data directories from that package layout.
SQLite is the actual library linked into the selected Python interpreter.
To use a different Python environment, set `COMPARISON_PYTHON=/path/to/python`;
it must contain psycopg3 with working libpq support.

```sh
python3 -B -m unittest discover -s experiments/database-comparison -p test_suite.py -v
python3 -B experiments/database-comparison/materialize.py --check
experiments/database-comparison/run.sh --output build/database-comparison-new
```

The output must be new and under `build/`. The shell runner holds
`/tmp/jaydb2-experiments-heavy.lock` throughout the fresh release build and all
measurements. Do not wrap it in another lock on that file. Construction of the
project sources used parallel subagents; measurements run serially and rotate
engine order across scenarios. Other unrelated machine activity is not locked.

Use `--scenarios 04_ecommerce`, `--engines jaydb2 sqlite`, `--samples 7`, and
`--warmups 1` for documented subsets. At least two measured samples are required.
The default runs all 30 databases, one client at a time, with durable commits:
SQLite STRICT/WAL/FULL and enabled FKs, PostgreSQL fsync/synchronous commit, and
JayDB2 complete-image persistence, one native worker and one reader. Every
population insert commits separately. Warmups are retained and excluded from
summaries. Timings cover the Python API call, encoding and decoding included.

Each workload checks an independent in-memory model: a point read, point update,
atomic two-row update, whole-table SUM, and a relationship projection for the
nine multi-table projects. SQL uses native SUM/JOIN. JayDB2's deliberately simple
adapter composes 9/17 prepared service requests for the eight-row SUM/JOIN;
these are client workflow comparisons. Both operations could be implemented
inside a custom certified Bend program. They are not concurrency-safe snapshots
in this adapter. Full initial and post-reopen data validation uses a separate
certified six-cell read program outside timed samples.

The runner checks wrong-type rejection, rollback after a valid first write and
invalid second write, missing reads, insert/delete, duplicate-key behavior,
orphan-reference behavior, and every final field after reopening. JayDB2 is
actually restarted and re-prepared; SQLite is closed/reopened; PostgreSQL first
reconnects clients and then restarts the entire private cluster and checks all
databases again. These are orderly restart checks, not crash or power-fail tests.

JayDB2 uses `Free.configuration`: authentication, schema validation, technical
limits and real proof admission remain, but no application foreign-key or
permission laws are installed. SQL foreign keys are real constraints. The suite
records that semantic gap rather than declaring all three schemas equivalent.
`DefineRow` is also an upsert, unlike the strict SQL INSERT used for population.

Output includes `result.json` with raw samples, checks, source and scenario
hashes, hardware, actual versions and build identity; per-project results and
final JSON data; SQLite files; JayDB2 storage; and the stopped PostgreSQL cluster
with SQL dumps. The run records a dirty-checkout patch and snapshots its suite.
Production/tool and suite identities must remain stable throughout measurement.
Pre-existing user modifications are included in provenance and never committed
by this experiment. Prepared programs still pass the real checker/compiler path.

Memory is sampled process-tree RSS at 10 ms during timed workloads only: JayDB2
controller and descendants, entire PostgreSQL cluster, or the Python harness
including embedded SQLite. These scopes differ; shared pages are counted per
process and short peaks can be missed. Disk sizes similarly include different
overheads (PG catalogs, live SQLite WAL/SHM, JayDB2 snapshot versus executable
cache). Neither metric supports a database efficiency ranking by itself.

JayDB2's persisted environment must match its original executable exactly. Keep
the recorded binary, staged sources/toolchain and storage together. Rebuilding
another revision is not a supported migration or reopen procedure.

Regenerate project artifacts after changing common sources or scenarios:

```sh
python3 -B experiments/database-comparison/materialize.py
```

After a completed run, recompute retained statistics and charts with the analysis
script (requires `matplotlib==3.11.2` in the selected Python environment):

```sh
python3 experiments/database-comparison/analyze.py build/database-comparison-final/result.json
```

It validates every stored timing summary against checked samples and keeps
completed engine failures visible. Failed/partial runs with a fatal top-level
error cannot produce passing performance evidence.
