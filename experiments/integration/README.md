# Combined experiment

This branch combines the accepted experiments before any merge to `main`.
Individual experiment reports describe their own recorded revisions; they do
not establish that the combined revision passed those same checks. See
`REPORT.md` for the checks actually run here.

Included:

- Reproducible baseline tools and removal of the redundant decoder process.
- Optional complete-state persistence, with explicit create/open and fatal
  uncertainty at the durable commit boundary.
- Optional ordinary library helpers, unique-key indexes, explicit derived-table
  scans/maintenance, and ordinary receipt tables/laws.
- Bounded FIFO input scheduling and certified prepared CPU read batches.
- Optional administrator elapsed-service-time records, including concurrent
  completion before FIFO response delivery.

GPU execution and the Bend host replacement remain separate experiments.
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
flock /tmp/jaydb2-experiments-heavy.lock make verify-contract verify
flock /tmp/jaydb2-experiments-heavy.lock make test
flock /tmp/jaydb2-experiments-heavy.lock make test-library
flock /tmp/jaydb2-experiments-heavy.lock make test-persistence
flock /tmp/jaydb2-experiments-heavy.lock make test-idempotency test-idempotency-recovery
```

Benchmark runners that take the common lock themselves must be called directly,
without an outer `flock`.
