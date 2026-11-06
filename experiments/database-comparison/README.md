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

New runs compare outputs recursively with exact primitive types: `True` differs
from `1`, including inside nested lists and records. This equality policy is
recorded in settings. It strengthens validation without changing the timed
workloads or historical result files.

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

The retained 6 November run has a special, explicit provenance audit: another
session added two contract modules after the measured services had frozen their
sources, tripping the repository-wide inventory guard. All original bytes and
all ten stored environment hashes were verified independently. The raw guard
failure remains in [evidence/raw-result.json](evidence/raw-result.json); the
[evidence notes](evidence/README.md) explain the derived analysis input.
With the original run files and matching experiment checkout, reproduce it with:

```sh
python3 experiments/database-comparison/audit.py \
  build/database-comparison-final/result.json \
  --derived build/database-comparison-analysis/audited-result.json \
  --evidence experiments/database-comparison/evidence
python3 experiments/database-comparison/analyze.py \
  build/database-comparison-analysis/audited-result.json
```

Use a dedicated checkout for future measurements; the runner intentionally
rejects repository inventory changes rather than silently ignoring them.

## Reuse as a performance regression benchmark

Keep this directory, its ten canonical fixtures, and the historical evidence in
version control. Measure from dedicated checkouts so another task cannot change
the engine mid-run. Preserve the executable recorded by each run: a subsequent
build in the same checkout can replace that binary, making its old persistent
databases impossible to reopen under the exact-environment contract.

For a quick end-to-end comparison, run the same explicit subset and settings
before and after an engine change, each with a fresh output directory:

```sh
experiments/database-comparison/run.sh \
  --scenarios 01_personal_tasks 04_ecommerce 10_municipal_services \
  --samples 7 --warmups 1 --output build/performance-before
# Implement and verify the engine change; retain the baseline executable.
experiments/database-comparison/run.sh \
  --scenarios 01_personal_tasks 04_ecommerce 10_municipal_services \
  --samples 7 --warmups 1 --output build/performance-after
python3 experiments/database-comparison/compare.py \
  build/performance-before/result.json build/performance-after/result.json \
  --output build/performance-comparison \
  --noise-percent 5 --fail-regression-percent 15
```

Run all ten projects for the final comparison. The same utility also accepts
JayDB2-only runs (`run.sh --engines jaydb2`) for quicker engine development,
but those runs cannot establish an advantage over the SQL engines. An explicit
`compare.py --engines jaydb2` selects which engines gate a comparison; selected
engines must exist on both sides, and their scenario sets must match exactly.

`compare.py` writes `comparison.json` and `comparison.md` with every paired
scenario/workload, setup measurements, failed database checks, integrity-behavior
changes, binary/source identities, tool versions, and hardware. It recomputes
medians, p95 and MAD from checked raw samples rather than trusting stored
summaries. It rejects incomplete/fatal runs, duplicate or missing records,
changed schemas or seed rows, changed sample counts/settings, and unchecked or
incorrect results. It never pools away a slow scenario or produces a composite
score with adjustable workload weights.

The default gate fails when a selected workload median slows by more than 15%,
when a selected database fails, or when duplicate-key/foreign-key behavior
changes. Setup changes are always displayed and can also be gated using
`--gate-metrics latency setup`; each setup value has only one observation.
Changes inside 5% are labeled `within_tolerance`; slowdowns between 5% and 15%
remain visible as `possible_regression`. These are configurable engineering
thresholds, not statistical-significance tests. A passing finite benchmark
cannot prove the absence of regressions; repeat suspicious/noisy measurements
and run the correctness, proof, recovery and application regression gates too.

Measured adapters, driver, sampler, actual root Bend programs, and fixture
identities must normally match. The legacy profile reads root `Access.bend`,
`Batch.bend`, and `ReadRow.bend`; unused `query/` additions and generated
`projects/` copies are excluded from its measured-source comparison. A nonlegacy
profile additionally checks its `query/` Python/Bend sources.
`--allow-workload-change` makes application-profile experiments
explicit and labels them as such: they do not isolate an engine optimization.
It permits different `settings.profile` and `settings.profile_metadata` while
retaining both values and a warning. An absent historical profile means
`legacy`. All other measured settings, including samples, warmups, durability,
client count, native threads, readers and exact-type equality, remain identical.
`--allow-environment-change` similarly reports changed tools, versions or
hardware instead of attributing all differences to the engine. Neither option
permits changed scenario hashes, nonprofile settings or workload coverage. This prevents
an apparent win obtained by reducing durability, omitting work, changing data,
or silently substituting a different query implementation.

Lightweight checks for the reusable comparison and type-aware result validator:

```sh
python3 -B -m unittest discover -s experiments/database-comparison -p 'test_*.py' -v
```

CLI exit codes are 0 for a passed configured gate, 1 for a failed gate, and 2
for invalid/incompatible inputs. Output directories must be new, preserving
earlier evidence and making this suitable for an optional CI performance job.

For a three-run follow-up containing a baseline, an unchanged-workload engine
candidate and the optional `single-call-queries-v1` profile, create combined
JSON, Markdown, PNG/SVG and HTML evidence with:

```sh
/path/to/python-with-matplotlib experiments/database-comparison/performance_report.py \
  build/performance-before/result.json build/performance-after/result.json \
  build/comparison-single-call-queries/result.json --output build/performance-summary
```

The summary requires all thirty databases to pass in each run, validates matched
settings/profile identities using the comparator, and checks final data hashes
across all nine matching engine/run records per scenario. Its output directory
must be new. Run `compare.py` separately for configured latency/setup gate results;
the visual summary exposes measurements and does not replace those gates.
