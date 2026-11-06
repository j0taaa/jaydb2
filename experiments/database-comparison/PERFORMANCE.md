# Verified performance improvements

The original ten-scenario benchmark is retained unchanged as a historical
report. This follow-up starts from engine revision `441f807` plus that saved
suite and uses separate frozen baseline/candidate checkouts. Final repeated
results and release-check evidence will be recorded here after completion.

## Implemented changes and preserved behavior

The original `Bytes.nat64` converts a natural through one predecessor step per
unit. `Input.parts` previously performed that conversion on the configured
state and message ceilings in every authentication and execution worker. The
8 MiB ceiling therefore caused millions of conversion steps even with tiny
stored data. The benchmark keeps that same ceiling.

`FastBytes.nat64_checked` uses the official U32 conversion and an exact natural
roundtrip guard. Values through `U32::MAX` use the short native path; larger
values try a two-word candidate checked against its exact fixed-width natural
measure. Values outside these guarded paths use a tail-recursive conversion.
The checked shortcuts and tail fallback are proved equal to the original for every natural,
including overflow. No arithmetic axiom, compiler change, truncated comparison,
cached answer or smaller logical limit is introduced.

`OptimizedInput` changes only the conversion used in input composition. Checked
theorems establish exact equality of parts, decode, analyze and private
authentication output to the original input machine for every packet, schema
and limits, without valid-input or credential assumptions. Native ordinary,
prepared and read-only entries use this equivalent input route. The original
contract and eight-law model functions remain unchanged. Rust, Node, C, the
official compiler/runtime, OS and storage assumptions retain their documented
trusted-boundary status.

Explicitly read-only-certified prepared requests now use the existing pinned
durable-root path with one reader as well as multiple readers. This remains
serial with one reader. It preserves fresh authentication, sealed artifacts,
native execution, changed-state rejection, response pairing and FIFO barriers.
Ordinary and write-capable requests retain their original publication path.

An additional `single-call-queries-v1` application profile executes generic SUM
and child-parent JOIN inside one certified transaction instead of nine or
seventeen requests. Actual key lists drive both traversal and termination;
there is no eight-row bound or cached data. Its Reader and validation program
have genuine read-only certificates; SUM/JOIN retain ordinary admission with
actual-state termination. All six program preparation costs remain measured.
This profile is reported separately from the engine-only comparison.

## Validation status

Focused proofs pass both official modes, including the complete existing
contract/implementation/library proof aggregate. Rust unit checks, exact-type
benchmark comparisons and application-wrapper unit checks pass. Full native,
durability/recovery, application and release validation are queued behind the
frozen baseline benchmark. No final performance or regression conclusion is
claimed until those checks and the candidate measurements complete.

The benchmark is now discoverable from the repository README, has Make targets,
and runs fixture/comparator checks in smoke and full CI. The comparison reports
every scenario/workload and setup result, with configurable noise and regression
thresholds; it does not invent an aggregate score or hide losses. Passing finite
tests and a sampled gate cannot establish absence of every possible regression.

## Measurement controls

Three complete runs use the same ten schema/data fixtures and the same oracle:
1/3/5/8/10/12/15/18/22/26 tables, eight rows per table, seven measured samples
and one warmup per workload, one client, one native thread and one reader.
The five workflows cover point reads, point updates, atomic two-row updates,
SUM and the nine applicable child-parent JOINs. Each timed result is checked
recursively with exact types. Every final cell is checked after reopening;
PostgreSQL also undergoes a complete private-cluster restart.

The baseline uses engine revision `441f807` plus the saved benchmark. The engine
candidate keeps the original measured adapter and programs. The additional
query-profile run changes only the explicitly recorded application strategy.
Its comparisons require `--allow-workload-change`; its preparation costs must
not be attributed to an isolated engine improvement.

All three use durable writes and the original 8 MiB state, 256 KiB message and
256 KiB response ceilings. PostgreSQL uses synchronous commit/fsync and SQLite
uses STRICT tables, WAL/FULL and real foreign keys. JayDB2 continues fresh
native workers, fresh authentication, actual source-bound proof admission and
sealed artifact verification. The common heavy-work lock serializes native
validation and measurements, but cannot control unrelated machine activity.

The report aggregates an unweighted median of each scenario's sample median.
A paired speedup is computed separately for each matching scenario, then its
median is reported. Those two aggregations need not have identical ratios.
Every scenario/workload and setup observation remains in the comparison files.
There is no adjustable composite score. Seven-sample nearest-rank p95 is the
sample maximum, not a reliable population tail estimate.

## Costs and limits to retain

This is a schema-feasibility and access-path study, not a large-data scaling or
concurrent-throughput benchmark. Tiny data favors fixed-cost analysis and does
not establish performance at the configured state ceiling. Setup, compilation,
initial population and reopen preparation are measured separately from warmed
workload calls. Setup has one observation per scenario, so individual changes
need cautious interpretation under changing host load.

The additional application profile prepares six programs instead of three.
Its SUM/JOIN programs have actual-observation termination and universal Free
policy certificates; those certificates do not prove query-result mathematics
or supply arbitrary application laws. Native edge-case checks and independent
benchmark oracles verify actual outputs. Intermediate signed64 SUM overflow
refuses, whereas PostgreSQL SUM(bigint) uses a numeric accumulator. All fixture
sums fit the common signed64 subset.

JayDB2's benchmark configuration installs no business or permission laws.
SQL foreign keys therefore remain stronger than this JayDB2 configuration,
and DefineRow retains its existing replacement behavior rather than strict
INSERT behavior. These differences are exposed by negative probes and are
unchanged by the optimization. Existing restricted-user application tests
remain part of validation.

The native Nat domain remains 48 bits, independent of full two-word signed64
stored values. The fast conversion is logically equal for every natural;
native boundary tests cover the supported domain. Initial configuration
validation still follows its existing startup path. The singleton certified
read path uses the existing batch observer/timing events, including
`read_batch: true`; it omits the former serial prepared-resolution intermediate
inspector event. Public response, authentication and FIFO behavior are retained.

RSS is sampled every 10 ms and may miss short peaks; summed process-tree RSS
counts shared pages repeatedly. Engine process scopes and storage accounting
also differ. Neither sampled RSS nor disk size alone supports an efficiency
ranking. The exact executable/environment is part of a JayDB2 durable database;
retain each run's matching executable and do not treat a newer build as a
supported migration.

## Further work that needs its own design and evidence

After these changes, useful candidates include profiling the remaining worker
startup and state-codec costs, proving indexed lookup implementations, and
extending read-only certification to actual-observation traversals. Each needs
measured evidence and its own preservation argument. This change does not skip
authentication, cache identity or results, weaken artifact checks, lower limits,
change the official compiler/runtime, or introduce long-lived workers. No
claim that JayDB2 beats the SQL engines follows from a JayDB2-only improvement.
