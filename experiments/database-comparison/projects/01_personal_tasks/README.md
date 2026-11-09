# Personal task planner

A single-user planner with priorities, completion state, deadlines, and effort estimates.

This project has 1 tables and 8 deterministic seed rows. The [canonical scenario](../../scenarios/01_personal_tasks.json) contains the schema, literal rows, workload metadata, and domain limitations.

Look up and revise the effort estimate for the last task; total the planned minutes across all tasks.

| Table | Rows | Columns | References |
| --- | ---: | --- | --- |
| `tasks` | 8 | `id` (text), `title` (text), `priority` (integer), `completed` (boolean), `due_on` (text), `estimated_minutes` (integer) | — |

The point-read and update target is `tasks.estimated_minutes` where `id = 'task_008'`. The aggregate sums `tasks.estimated_minutes`. The transaction workload updates two existing rows atomically.

This single-table project has no relationship-join workload.

The `jaydb2/` directory contains the actual configuration, empty application-table seed with a benchmark user, generic access, two-write, and six-cell row-read programs, and their universal certificates and termination proofs. The row-read program batches untimed full-data validation into one certified transaction per row; it is separate from the timed point-read and relationship workloads. Each project has eleven generated files: eight Bend sources, two SQL schemas, and this README. The runner inserts the canonical rows through admitted prepared requests; the seed file does not embed those rows. Relative Bend dependencies are supplied by the existing service staging path.

JayDB2 uses the permissive `Free` configuration: technical schema checks and authentication apply, but no administrator laws enforce foreign keys or domain invariants. The SQLite and PostgreSQL schemas declare real foreign-key constraints. SQLite additionally uses STRICT tables and Boolean checks; the runner enables `PRAGMA foreign_keys=ON`. These are explicit differences in integrity semantics.

Run this scenario on all three engines from the repository root:

```sh
experiments/database-comparison/run.sh \
  --scenarios 01_personal_tasks --output build/comparison-01_personal_tasks
```

Use a new output directory for each run. The runner owns the live databases and records correctness checks, setup costs, timings, storage, and restart behavior there. The source artifacts in this directory are generated for review.

Modeling limits:

- Dates are ISO 8601 date strings; all tasks belong to one implicit user.
- Priority 1 means highest urgency; priority range and nonnegative effort are application conventions, not declared constraints.
- Eight rows exercise API feasibility, not production scale.

Regenerate all projects after changing scenario definitions or the common adapters:

```sh
python3 -B experiments/database-comparison/materialize.py
python3 -B experiments/database-comparison/materialize.py --check
```
