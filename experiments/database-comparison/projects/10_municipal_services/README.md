# Municipal service administration

Municipal operations tie residents, properties, permits, requests, inspections, work orders, contracts, budgets, and fees to responsible departments.

This project has 26 tables and 208 deterministic seed rows. The [canonical scenario](../../scenarios/10_municipal_services.json) contains the schema, literal rows, workload metadata, and domain limitations.

Receive a resident request, issue and inspect permits, schedule contracted asset work, assign staff and materials, post the expense, and collect permit fees.

| Table | Rows | Columns | References |
| --- | ---: | --- | --- |
| `districts` | 8 | `id` (text), `name` (text), `population` (integer) | — |
| `departments` | 8 | `id` (text), `district_id` (text), `name` (text), `annual_budget_cents` (integer) | `district_id` → `districts.id` |
| `staff` | 8 | `id` (text), `department_id` (text), `full_name` (text), `role` (text) | `department_id` → `departments.id` |
| `residents` | 8 | `id` (text), `district_id` (text), `full_name` (text), `birth_year` (integer) | `district_id` → `districts.id` |
| `addresses` | 8 | `id` (text), `district_id` (text), `street` (text), `number` (integer) | `district_id` → `districts.id` |
| `properties` | 8 | `id` (text), `address_id` (text), `owner_id` (text), `property_kind` (text), `assessed_value_cents` (integer) | `address_id` → `addresses.id`, `owner_id` → `residents.id` |
| `service_categories` | 8 | `id` (text), `department_id` (text), `name` (text), `target_days` (integer) | `department_id` → `departments.id` |
| `service_requests` | 8 | `id` (text), `resident_id` (text), `property_id` (text), `category_id` (text), `opened_date` (text), `status` (text) | `resident_id` → `residents.id`, `property_id` → `properties.id`, `category_id` → `service_categories.id` |
| `request_updates` | 8 | `id` (text), `request_id` (text), `staff_id` (text), `message` (text), `update_date` (text) | `request_id` → `service_requests.id`, `staff_id` → `staff.id` |
| `permit_types` | 8 | `id` (text), `department_id` (text), `name` (text), `base_fee_cents` (integer) | `department_id` → `departments.id` |
| `permit_applications` | 8 | `id` (text), `property_id` (text), `resident_id` (text), `permit_type_id` (text), `submitted_date` (text) | `property_id` → `properties.id`, `resident_id` → `residents.id`, `permit_type_id` → `permit_types.id` |
| `permits` | 8 | `id` (text), `application_id` (text), `approved_by` (text), `issued_date` (text), `valid_days` (integer) | `application_id` → `permit_applications.id`, `approved_by` → `staff.id` |
| `inspection_types` | 8 | `id` (text), `department_id` (text), `name` (text), `checklist_items` (integer) | `department_id` → `departments.id` |
| `inspections` | 8 | `id` (text), `property_id` (text), `inspection_type_id` (text), `inspector_id` (text), `inspection_date` (text), `result` (text) | `property_id` → `properties.id`, `inspection_type_id` → `inspection_types.id`, `inspector_id` → `staff.id` |
| `violations` | 8 | `id` (text), `inspection_id` (text), `code` (text), `fine_cents` (integer), `status` (text) | `inspection_id` → `inspections.id` |
| `vendors` | 8 | `id` (text), `name` (text), `registration` (text) | — |
| `contracts` | 8 | `id` (text), `vendor_id` (text), `department_id` (text), `description` (text), `ceiling_cents` (integer) | `vendor_id` → `vendors.id`, `department_id` → `departments.id` |
| `assets` | 8 | `id` (text), `department_id` (text), `address_id` (text), `name` (text), `replacement_cost_cents` (integer) | `department_id` → `departments.id`, `address_id` → `addresses.id` |
| `work_orders` | 8 | `id` (text), `request_id` (text), `contract_id` (text), `asset_id` (text), `scheduled_date` (text), `estimated_cost_cents` (integer) | `request_id` → `service_requests.id`, `contract_id` → `contracts.id`, `asset_id` → `assets.id` |
| `work_order_assignments` | 8 | `id` (text), `work_order_id` (text), `staff_id` (text), `planned_hours` (integer) | `work_order_id` → `work_orders.id`, `staff_id` → `staff.id` |
| `material_catalog` | 8 | `id` (text), `name` (text), `unit` (text), `unit_cost_cents` (integer) | — |
| `work_order_materials` | 8 | `id` (text), `work_order_id` (text), `material_id` (text), `quantity` (integer) | `work_order_id` → `work_orders.id`, `material_id` → `material_catalog.id` |
| `budget_accounts` | 8 | `id` (text), `department_id` (text), `fiscal_year` (integer), `account_code` (text), `allocated_cents` (integer) | `department_id` → `departments.id` |
| `expenditures` | 8 | `id` (text), `budget_account_id` (text), `work_order_id` (text), `posted_date` (text), `amount_cents` (integer) | `budget_account_id` → `budget_accounts.id`, `work_order_id` → `work_orders.id` |
| `fee_invoices` | 8 | `id` (text), `resident_id` (text), `permit_id` (text), `issued_date` (text), `total_cents` (integer) | `resident_id` → `residents.id`, `permit_id` → `permits.id` |
| `fee_payments` | 8 | `id` (text), `fee_invoice_id` (text), `received_date` (text), `method` (text), `amount_cents` (integer) | `fee_invoice_id` → `fee_invoices.id` |

The point-read and update target is `expenditures.amount_cents` where `id = 'expenditures_08'`. The aggregate sums `expenditures.amount_cents`. The transaction workload updates two existing rows atomically.

The relationship workload joins `service_requests.category_id` to `service_categories.id` and returns `[service_requests.id, service_categories.name]` in child-ID order. SQL runs a native join; JayDB2 composes key enumeration and cell reads in the client.

The `jaydb2/` directory contains the actual configuration, empty application-table seed with a benchmark user, generic access, two-write, and six-cell row-read programs, and their universal certificates and termination proofs. The row-read program batches untimed full-data validation into one certified transaction per row; it is separate from the timed point-read and relationship workloads. Each project has eleven generated files: eight Bend sources, two SQL schemas, and this README. The runner inserts the canonical rows through admitted prepared requests; the seed file does not embed those rows. Relative Bend dependencies are supplied by the existing service staging path.

JayDB2 uses the permissive `Free` configuration: technical schema checks and authentication apply, but no administrator laws enforce foreign keys or domain invariants. The SQLite and PostgreSQL schemas declare real foreign-key constraints. SQLite additionally uses STRICT tables and Boolean checks; the runner enables `PRAGMA foreign_keys=ON`. These are explicit differences in integrity semantics.

Run this scenario on all three engines from the repository root:

```sh
experiments/database-comparison/run.sh \
  --scenarios 10_municipal_services --output build/comparison-10_municipal_services
```

Use a new output directory for each run. The runner owns the live databases and records correctness checks, setup costs, timings, storage, and restart behavior there. The source artifacts in this directory are generated for review.

Modeling limits:

- All residents and locations are synthetic. Money is integer BRL cents and dates are ISO text. The violation table includes cleared observations with zero fines so every inspection has a representative record. Public-record disclosure, personal-data protection, legal deadlines, appeals, procurement compliance, multi-year appropriations, and audit authorization require a broader design.

Regenerate all projects after changing scenario definitions or the common adapters:

```sh
python3 -B experiments/database-comparison/materialize.py
python3 -B experiments/database-comparison/materialize.py --check
```
