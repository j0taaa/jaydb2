# Specialty coffee ecommerce fulfillment

An eight-table retailer model for product catalog, stock by warehouse, customer orders and settlements. The fixture contains fully paid orders whose line totals agree with their order and payment amounts.

This project has 8 tables and 64 deterministic seed rows. The [canonical scenario](../../scenarios/04_ecommerce.json) contains the schema, literal rows, workload metadata, and domain limitations.

Read and correct stock on hand, total stock across warehouses, and resolve order lines to product display names.

| Table | Rows | Columns | References |
| --- | ---: | --- | --- |
| `customers` | 8 | `id` (text), `name` (text), `email` (text), `country_code` (text) | — |
| `categories` | 8 | `id` (text), `name` (text), `department` (text) | — |
| `products` | 8 | `id` (text), `category_id` (text), `name` (text), `price_cents` (integer), `active` (boolean) | `category_id` → `categories.id` |
| `warehouses` | 8 | `id` (text), `name` (text), `city` (text), `active` (boolean) | — |
| `inventory` | 8 | `id` (text), `product_id` (text), `warehouse_id` (text), `quantity` (integer), `reorder_level` (integer) | `product_id` → `products.id`, `warehouse_id` → `warehouses.id` |
| `orders` | 8 | `id` (text), `customer_id` (text), `status` (text), `ordered_at` (text), `total_cents` (integer) | `customer_id` → `customers.id` |
| `order_items` | 8 | `id` (text), `order_id` (text), `product_id` (text), `quantity` (integer), `unit_price_cents` (integer) | `order_id` → `orders.id`, `product_id` → `products.id` |
| `payments` | 8 | `id` (text), `order_id` (text), `method` (text), `amount_cents` (integer), `status` (text) | `order_id` → `orders.id` |

The point-read and update target is `inventory.quantity` where `id = 'stock_gift_cwb'`. The aggregate sums `inventory.quantity`. The transaction workload updates two existing rows atomically.

The relationship workload joins `order_items.product_id` to `products.id` and returns `[order_items.id, products.name]` in child-ID order. SQL runs a native join; JayDB2 composes key enumeration and cell reads in the client.

The `jaydb2/` directory contains the actual configuration, empty application-table seed with a benchmark user, generic access, two-write, and six-cell row-read programs, and their universal certificates and termination proofs. The row-read program batches untimed full-data validation into one certified transaction per row; it is separate from the timed point-read and relationship workloads. Each project has eleven generated files: eight Bend sources, two SQL schemas, and this README. The runner inserts the canonical rows through admitted prepared requests; the seed file does not embed those rows. Relative Bend dependencies are supplied by the existing service staging path.

JayDB2 uses the permissive `Free` configuration: technical schema checks and authentication apply, but no administrator laws enforce foreign keys or domain invariants. The SQLite and PostgreSQL schemas declare real foreign-key constraints. SQLite additionally uses STRICT tables and Boolean checks; the runner enables `PRAGMA foreign_keys=ON`. These are explicit differences in integrity semantics.

Run this scenario on all three engines from the repository root:

```sh
experiments/database-comparison/run.sh \
  --scenarios 04_ecommerce --output build/comparison-04_ecommerce
```

Use a new output directory for each run. The runner owns the live databases and records correctness checks, setup costs, timings, storage, and restart behavior there. The source artifacts in this directory are generated for review.

Modeling limits:

- All monetary values are integer BRL cents; dates are ISO 8601 text. No tax, discounts, shipping charges or currency conversion are modeled.
- The small fixture has one line and one settlement per order; the schema permits multiple lines and payments.
- Foreign keys describe relationships, but stock nonnegativity and equality between order, line and settlement totals need additional constraints or application laws.
- No sensitive customer data is real; example.test addresses and names are synthetic.

Regenerate all projects after changing scenario definitions or the common adapters:

```sh
python3 -B experiments/database-comparison/materialize.py
python3 -B experiments/database-comparison/materialize.py --check
```
