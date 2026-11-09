# Household budget ledger

Accounts, spending categories, and posted ledger entries for a Brazilian household.

This project has 3 tables and 24 deterministic seed rows. The [canonical scenario](../../scenarios/02_household_budget.json) contains the schema, literal rows, workload metadata, and domain limitations.

Correct a posted amount, total net cash flow, and attach category names to the ledger entries.

| Table | Rows | Columns | References |
| --- | ---: | --- | --- |
| `accounts` | 8 | `id` (text), `name` (text), `kind` (text), `currency` (text), `opening_balance_cents` (integer), `active` (boolean) | — |
| `categories` | 8 | `id` (text), `name` (text), `monthly_budget_cents` (integer), `essential` (boolean) | — |
| `transactions` | 8 | `id` (text), `account_id` (text), `category_id` (text), `description` (text), `amount_cents` (integer), `posted_on` (text) | `account_id` → `accounts.id`, `category_id` → `categories.id` |

The point-read and update target is `transactions.amount_cents` where `id = 'txn_008'`. The aggregate sums `transactions.amount_cents`. The transaction workload updates two existing rows atomically.

The relationship workload joins `transactions.category_id` to `categories.id` and returns `[transactions.id, categories.name]` in child-ID order. SQL runs a native join; JayDB2 composes key enumeration and cell reads in the client.

The `jaydb2/` directory contains the actual configuration, empty application-table seed with a benchmark user, generic access, two-write, and six-cell row-read programs, and their universal certificates and termination proofs. The row-read program batches untimed full-data validation into one certified transaction per row; it is separate from the timed point-read and relationship workloads. Each project has eleven generated files: eight Bend sources, two SQL schemas, and this README. The runner inserts the canonical rows through admitted prepared requests; the seed file does not embed those rows. Relative Bend dependencies are supplied by the existing service staging path.

JayDB2 uses the permissive `Free` configuration: technical schema checks and authentication apply, but no administrator laws enforce foreign keys or domain invariants. The SQLite and PostgreSQL schemas declare real foreign-key constraints. SQLite additionally uses STRICT tables and Boolean checks; the runner enables `PRAGMA foreign_keys=ON`. These are explicit differences in integrity semantics.

Run this scenario on all three engines from the repository root:

```sh
experiments/database-comparison/run.sh \
  --scenarios 02_household_budget --output build/comparison-02_household_budget
```

Use a new output directory for each run. The runner owns the live databases and records correctness checks, setup costs, timings, storage, and restart behavior there. The source artifacts in this directory are generated for review.

Modeling limits:

- All money uses integer BRL cents and every account has the same currency.
- Amounts are positive for income and negative for spending; this is a personal cash-flow ledger, not double-entry accounting.
- Account balances are opening balances; no stored running-balance synchronization is claimed.
- Eight rows per table are a small deterministic functional fixture.

Regenerate all projects after changing scenario definitions or the common adapters:

```sh
python3 -B experiments/database-comparison/materialize.py
python3 -B experiments/database-comparison/materialize.py --check
```
