# Generic single-transaction SUM and relationship JOIN

These are an additional application profile; the historical benchmark programs,
raw samples and scores remain unchanged. Both programs enumerate the actual table
keys and visit every returned key within one certified program invocation. They
have no eight-row bound, cached answers, hard-coded entity names or host-side
result computation.

Prepare each program with ordinary universal opcode **0**, using its matching
`SumProof.bend` or `JoinProof.bend`, then execute its handle normally. The source
files use only the contract/runtime modules already available in service staging;
the proof embeds the generic actual-observation completion bridge from the existing
indexed application's `Completion.bend`. No extra administrator dependency is
required.

- `Sum.bend` takes `["sum", table, integer_column]`. Empty tables return integer
  zero. It adds exact two-word signed64 values, checks signed overflow and refuses
  overflow or noninteger cells rather than wrapping or coercing them. Intermediate
  signed64 overflow refuses even if later values could bring the mathematical sum
  back into range. This is intentionally narrower than PostgreSQL's unbounded
  numeric accumulator for `SUM(bigint)`.
- `Join.bend` takes `["join", child_table, foreign_key_column, parent_table,
  parent_value_column]`. It returns `[[child_id, parent_value], ...]` in child-key
  order. Repeated parent keys are supported. Like an inner join, a missing parent
  omits that child and continues with later rows. A nontext foreign key refuses.
  Other schema/access failures retain ordinary engine data-error semantics.

Both use a real universal `Free` administrator certificate and a termination
witness depending on the **actual** enumeration result. After enumeration, SUM
needs one access per key and JOIN at most two, then a terminal action. The proof
constructs that finite suffix for the observed list and lifts it through the
actual `Data.operate` result, including failure. It does not assume a list length
from the schema, seed or benchmark. Since `ReadOnly.Program` requires a fixed
finite witness covering arbitrarily long observations before enumeration, these
programs deliberately do **not** claim that certificate or use opcode 3. They
still execute one isolated transaction and publish one complete checked result.

The `Free` policy does not enforce application ownership or foreign keys. The
certificates establish the configured technical/policy obligations and actual
termination, not a formal functional-correctness theorem for the aggregate or
join. Native checks compare results with independent Python expected values.
The existing message/state/response limits still apply; a large join can fail a
response limit atomically rather than returning a truncated result.

With the caller holding `/tmp/jaydb2-experiments-heavy.lock`, run from the root:

```sh
python3 -B experiments/database-comparison/query/check.py \
  --output build/query-profile-check
```

This creates a real durable database, prepares the two actual source/proof pairs
through normal admission, and tests empty tables, thirteen rows, negative values,
exact signed64 endpoints, both overflow directions, repeated parent keys, missing
parents, noninteger sums and malformed arguments. Output must be a new directory.

For pure proof validation without native compilation or measurement, use:

```sh
python3 -B experiments/database-comparison/query/check.py \
  --output build/query-profile-proof --check-only
```

That mode stages the actual universal bindings, configuration and seed, then
runs the official `--check-only` and `--verdict` checks for SUM, JOIN, Reader and
the additionally certified ReadRow program. All four program/proof pairs passed
both checkers during development; the native mode is still necessary to validate
the real admission/compiler/runtime bridge.

## Separately labelled application profile

`optimized.py` reuses the existing runner's scenario data, logical workloads,
exact-type oracle, negative checks, warmups, sample order, size limits, durable
settings and timing boundaries. It changes only JayDB2's application access
strategy. It never edits the historical runner or rewrites historical scores.

The adapter admits six actual programs:

| Program | Preparation opcode | Role |
| --- | ---: | --- |
| Access | 0 | Original inserts, updates and deletes |
| Batch | 0 | Original atomic two-write transaction |
| ReadRow | 3 | Original six-cell validation, with a genuine depth-7 read-only certificate |
| Reader | 3 | One `ReadCell` or `EnumerateKeys`, with a depth-2 read-only certificate |
| Sum | 0 | Generic single-transaction integer aggregate |
| Join | 0 | Generic single-transaction child-parent inner join |

Reader receives `["read", table, key, column]` or `["keys", table]`. Its operation
selector can issue only `ReadCell` or `EnumerateKeys`, for every possible
argument, and every continuation immediately finishes. ReadRow's additional
certificate covers all six actual reads and all possible continuation results.
These two programs may use the certified pinned-root path even with one reader.
The SUM and JOIN proofs remain actual-state termination witnesses under ordinary
preparation; they do not claim a fixed-depth read-only certificate.

Every program is actually prepared once on initial startup and once after
service reopening. All six preparation costs remain inside setup measurements
and appear individually in `jay_setup`; ReadRow is never double-prepared.
Fresh authentication, source/proof binding, artifact validation, execution and
ordinary write durability remain enabled. There is no response cache or row-count
assumption. The existing full initial/final validation still checks every row.

Run from the repository root with the same Python environment as the baseline:

```sh
flock /tmp/jaydb2-experiments-heavy.lock \
  build/database-comparison-venv/bin/python -B \
  experiments/database-comparison/query/optimized.py \
  --output build/comparison-single-call-queries --samples 7 --warmups 1
```

Use a new output directory. Root manifests are tagged **before each save**,
including running or failed results, with
`settings.profile = "single-call-queries-v1"` and explicit `profile_metadata`.
The existing suite source hash map and saved suite snapshot include this
wrapper, its program sources and proofs. SQL adapters and original negative
integrity probes are unchanged.

Comparing this profile against the historical multi-call adapter is explicitly
an **application-profile comparison**, not an isolated engine optimization:

```sh
python3 experiments/database-comparison/compare.py \
  build/baseline/result.json build/comparison-single-call-queries/result.json \
  --output build/comparison-application-profile --allow-workload-change
```

Without that flag, comparison refuses changed profile metadata. Setup costs,
functional failures and sampled regressions remain visible. A faster measured
profile does not establish absence of regressions or production-scale capacity.
Run the wrapper's lightweight preparation/metadata integrity checks separately:

```sh
python3 -B -m unittest discover -s experiments/database-comparison/query \
  -p 'test_*.py' -v
```
