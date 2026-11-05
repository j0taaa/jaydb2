# Ordinary-table index benchmark

This is optional development tooling. It adds no host feature, index primitive,
automatic maintenance, or runtime dependency. Work products stay under `build/`.

## Decision

Keep optional unique-key `Index.lookup` and `Index.claim`. Several lookups in one
transaction can make them useful. One isolated lookup did not reliably improve
complete-request latency in the tested small states, because the extra table
also increases state transfer/validation work. Index maintenance adds writes.

The current nonunique representation did not show a reliable speed benefit in
these tests. A faster nonunique representation is deferred. Its full-table
query helper is now explicitly named `Index.scan_equal`, without a compatibility
alias. It remains available for ordinary derived-table consistency examples.
No keyed bucket representation is implemented by this change.

## Historical measured evidence

The files in `evidence/` retain the original measurements at library revision
`29eea03f5b0f898bfcc3a990b9dbc864097c821f`, before the `lookup_many` to `scan_equal`
API rename. They are not measurements of this follow-up revision. The copied
raw data is unchanged and checksummed in `evidence/SHA256SUMS`.

- `results.json`: single-query/update samples, state sizes, settings, controller
  SHA-256, hardware, toolchain identity and exact staged source hashes.
- `batch-results.json`: follow-up unique checks sharing a transaction, raw
  samples, positive/negative controls, submitted source/proof identities.
- `analysis.json`: paired ratio analysis and pinned-toolchain verification.
- `BENCHMARK.txt`: readable results and original commands.

The first suite checked 7,900 real requests; the batch follow-up checked 662.
The 8,562 total includes setup and validation, not just timed requests. Queries
used 8/64/256 business rows with 128-byte padding and 64 rows with 2,048-byte
padding. Each timing case used two warmups and nine measured samples. Variant
order rotates and alternates. Reported times include the complete prepared
frame exchange; preparation is recorded separately. Python encoding and result
checking are outside the measured interval. There is one CPU native worker,
no GPU and no persistence. This is one machine/run, not a general speed claim.

The no-index baseline holds identical business data and empty index tables. A
second control scans business rows with the index present. Actual `Index.lookup`,
`Index.scan_equal` (formerly `lookup_many`) and `Index.maintain` handle indexed
work. The single unique scan stops at its first match. The nonunique baseline
reads the group field once per business row and returns all matching row IDs.
The batch baseline enumerates keys once; all measured batch queries are misses,
so no early-exit advantage was withheld. Positive batch controls also return
complete correct matching IDs, ruling out an always-empty implementation.

Every initial base row and index entry is read back. Indexed-field updates
alternate actual values and are followed by base/new-index/removed-old-index
checks; nonunique queries check complete expected contents. Both variants are
supplied the old indexed values, excluding any extra old-value read from index
maintenance timing. A permissive, explicit zero-law benchmark configuration
isolates access mechanics; real official certificates/termination, admission,
authentication, artifact seals and technical validation remain enabled.
Existing restricted-user exact-index proofs are checked separately.

## Reproduce

From this worktree, with the pinned toolchain and normal build prerequisites:

```sh
experiments/library/index_benchmark/run.sh --smoke
experiments/library/index_benchmark/run.sh
```

The wrapper acquires `/tmp/jaydb2-experiments-heavy.lock` itself. Do not wrap it
in another acquisition of the same lock. It builds the actual controller,
stages the ordinary helpers, checks both programs in BOTH official modes,
runs real prepared requests and checks every response against a Python model.
`--smoke` uses eight rows and two samples to validate the runner, not performance.

Each invocation chooses a fresh ignored output directory. To choose one:

```sh
JAYDB_INDEX_BENCH_OUTPUT="$PWD/build/library/index-benchmark-custom" \
  experiments/library/index_benchmark/run.sh
```

The directory must not contain a prior `results.json`; evidence is not silently
overwritten. Setup, logs, staged modules, per-request journals and summaries are
kept there. Current reproductions use the new API name and record their own
working-tree patch, source hashes and executable identity.
