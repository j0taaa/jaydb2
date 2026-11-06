# Discrete manufacturing and procurement

A small industrial group links purchased materials and stock lots to bills of material, production work, quality results, and customer orders.

This project has 22 tables and 176 deterministic seed rows. The [canonical scenario](../../scenarios/09_manufacturing.json) contains the schema, literal rows, workload metadata, and domain limitations.

Procure and receive material lots, release a bill of material and work order, record machine production and inspection, then fulfill a customer order.

| Table | Rows | Columns | References |
| --- | ---: | --- | --- |
| `plants` | 8 | `id` (text), `name` (text), `city` (text) | — |
| `units_of_measure` | 8 | `id` (text), `code` (text), `description` (text) | — |
| `suppliers` | 8 | `id` (text), `name` (text), `lead_days` (integer) | — |
| `customers` | 8 | `id` (text), `name` (text), `credit_limit_cents` (integer) | — |
| `employees` | 8 | `id` (text), `plant_id` (text), `full_name` (text), `role` (text) | `plant_id` → `plants.id` |
| `work_centers` | 8 | `id` (text), `plant_id` (text), `name` (text), `hourly_cost_cents` (integer) | `plant_id` → `plants.id` |
| `materials` | 8 | `id` (text), `unit_id` (text), `sku` (text), `reorder_quantity` (integer) | `unit_id` → `units_of_measure.id` |
| `supplier_materials` | 8 | `id` (text), `supplier_id` (text), `material_id` (text), `unit_cost_cents` (integer) | `supplier_id` → `suppliers.id`, `material_id` → `materials.id` |
| `products` | 8 | `id` (text), `unit_id` (text), `sku` (text), `list_price_cents` (integer) | `unit_id` → `units_of_measure.id` |
| `bills_of_material` | 8 | `id` (text), `product_id` (text), `revision` (text), `active` (boolean) | `product_id` → `products.id` |
| `bom_components` | 8 | `id` (text), `bill_id` (text), `material_id` (text), `quantity` (integer) | `bill_id` → `bills_of_material.id`, `material_id` → `materials.id` |
| `warehouses` | 8 | `id` (text), `plant_id` (text), `name` (text) | `plant_id` → `plants.id` |
| `stock_lots` | 8 | `id` (text), `warehouse_id` (text), `material_id` (text), `supplier_id` (text), `quantity` (integer) | `warehouse_id` → `warehouses.id`, `material_id` → `materials.id`, `supplier_id` → `suppliers.id` |
| `machines` | 8 | `id` (text), `work_center_id` (text), `asset_tag` (text), `service_interval_hours` (integer) | `work_center_id` → `work_centers.id` |
| `work_orders` | 8 | `id` (text), `product_id` (text), `work_center_id` (text), `planned_quantity` (integer), `due_date` (text) | `product_id` → `products.id`, `work_center_id` → `work_centers.id` |
| `operations` | 8 | `id` (text), `work_order_id` (text), `machine_id` (text), `sequence` (integer), `planned_minutes` (integer) | `work_order_id` → `work_orders.id`, `machine_id` → `machines.id` |
| `production_runs` | 8 | `id` (text), `operation_id` (text), `employee_id` (text), `completed_quantity` (integer), `scrap_quantity` (integer) | `operation_id` → `operations.id`, `employee_id` → `employees.id` |
| `quality_checks` | 8 | `id` (text), `production_run_id` (text), `inspector_id` (text), `result` (text), `defect_count` (integer) | `production_run_id` → `production_runs.id`, `inspector_id` → `employees.id` |
| `purchase_orders` | 8 | `id` (text), `supplier_id` (text), `warehouse_id` (text), `ordered_date` (text), `total_cents` (integer) | `supplier_id` → `suppliers.id`, `warehouse_id` → `warehouses.id` |
| `purchase_order_lines` | 8 | `id` (text), `purchase_order_id` (text), `material_id` (text), `quantity` (integer), `unit_cost_cents` (integer) | `purchase_order_id` → `purchase_orders.id`, `material_id` → `materials.id` |
| `sales_orders` | 8 | `id` (text), `customer_id` (text), `ordered_date` (text), `total_cents` (integer), `status` (text) | `customer_id` → `customers.id` |
| `sales_order_lines` | 8 | `id` (text), `sales_order_id` (text), `product_id` (text), `quantity` (integer), `unit_price_cents` (integer) | `sales_order_id` → `sales_orders.id`, `product_id` → `products.id` |

The point-read and update target is `sales_order_lines.unit_price_cents` where `id = 'sales_order_lines_08'`. The aggregate sums `sales_order_lines.unit_price_cents`. The transaction workload updates two existing rows atomically.

The relationship workload joins `work_orders.product_id` to `products.id` and returns `[work_orders.id, products.sku]` in child-ID order. SQL runs a native join; JayDB2 composes key enumeration and cell reads in the client.

The `jaydb2/` directory contains the actual configuration, empty application-table seed with a benchmark user, generic access, two-write, and six-cell row-read programs, and their universal certificates and termination proofs. The row-read program batches untimed full-data validation into one certified transaction per row; it is separate from the timed point-read and relationship workloads. Each project has eleven generated files: eight Bend sources, two SQL schemas, and this README. The runner inserts the canonical rows through admitted prepared requests; the seed file does not embed those rows. Relative Bend dependencies are supplied by the existing service staging path.

JayDB2 uses the permissive `Free` configuration: technical schema checks and authentication apply, but no administrator laws enforce foreign keys or domain invariants. The SQLite and PostgreSQL schemas declare real foreign-key constraints. SQLite additionally uses STRICT tables and Boolean checks; the runner enables `PRAGMA foreign_keys=ON`. These are explicit differences in integrity semantics.

Run this scenario on all three engines from the repository root:

```sh
experiments/database-comparison/run.sh \
  --scenarios 09_manufacturing --output build/comparison-09_manufacturing
```

Use a new output directory for each run. The runner owns the live databases and records correctness checks, setup costs, timings, storage, and restart behavior there. The source artifacts in this directory are generated for review.

Modeling limits:

- Money uses integer BRL cents; material quantities use their referenced unit with whole-unit precision. Each bill and order has one representative line. Unit conversion, multi-level BOMs, yield accounting, inventory valuation, serial traceability, and enforceable material availability are beyond this fixture.

Regenerate all projects after changing scenario definitions or the common adapters:

```sh
python3 -B experiments/database-comparison/materialize.py
python3 -B experiments/database-comparison/materialize.py --check
```
