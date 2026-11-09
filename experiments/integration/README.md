# Combined experimental branch

`experiment-integration` is the shared experimental branch. It follows `main`
and adds the optional GPU backend. Stable accepted experiments, the optional
SQL/Drizzle frontend, the comparison suite and the TCC sources come from main.
The Bend host replacement stays on `experiment-bend-host` and is not included.

Individual experiment reports describe their own recorded revisions; they do
not establish that the combined revision passed those same checks. Current
composition and validation are recorded in `CURRENT.md`; `REPORT.md` preserves
the original historical acceptance record.

Included:

- Reproducible baseline tools and removal of the redundant decoder process.
- Optional complete-state persistence, with explicit create/open and fatal
  uncertainty at the durable commit boundary.
- Optional ordinary library helpers, unique-key indexes, explicit derived-table
  scans/maintenance, and ordinary receipt tables/laws.
- Bounded FIFO input scheduling and certified prepared CPU read batches.
- Optional administrator elapsed-service-time records, including concurrent
  completion before FIFO response delivery.

- Optional official CUDA execution, sealed device artifacts and failure rollback.

GPU execution stays on this experimental branch and `experiment-gpu`; it is not
part of `main`. The Bend host replacement remains separate.
Quota enforcement is excluded. There is no new nonunique index implementation:
`Index.scan_equal` remains an explicit full scan. No migrations or compatibility
framework are added; development snapshots require their exact environment and
controller executable.

`--read-workers` defaults to one. Parallel read execution is provisional until
fixed-total-CPU measurements justify keeping it. Writes, unknown programs and
prepared controls remain exclusive; the scheduler never searches past a writer
to fill a read batch.

The source revisions incorporated are in `SOURCES.json`. Some branches already
include earlier versions of their prerequisites; current fixes are reconciled
explicitly, rather than treating an old merge as evidence of current parity.

Run heavy checks under the common advisory lock:

```sh
ulimit -s unlimited
flock /tmp/jaydb2-experiments-heavy.lock make verify-contract verify
flock /tmp/jaydb2-experiments-heavy.lock make test
flock /tmp/jaydb2-experiments-heavy.lock make test-library
flock /tmp/jaydb2-experiments-heavy.lock make test-persistence
flock /tmp/jaydb2-experiments-heavy.lock make test-idempotency test-idempotency-recovery
flock /tmp/jaydb2-experiments-heavy.lock make test-feature-integration
flock /tmp/jaydb2-experiments-heavy.lock make test-recovery-integration
make test-gpu  # Takes the common lock itself; requires an NVIDIA CUDA device.
```

The direct fault-build tests need the launcher's unlimited soft stack setting,
as shown above. Use a short private `TMPDIR` when running tests with Unix sockets.

Benchmark runners that take the common lock themselves must be called directly,
without an outer `flock`.
