# Contract logistics and delivery

A third-party logistics operator manages customer stock, warehouses, carrier trips, shipments, tracking, and invoice charges.

This project has 18 tables and 144 deterministic seed rows. The [canonical scenario](../../scenarios/08_logistics.json) contains the schema, literal rows, workload metadata, and domain limitations.

Receive customer stock, allocate shipment items, route a carrier trip, record tracking and delivery attempts, and bill the shipment.

| Table | Rows | Columns | References |
| --- | ---: | --- | --- |
| `customers` | 8 | `id` (text), `name` (text), `billing_email` (text) | — |
| `warehouses` | 8 | `id` (text), `name` (text), `city` (text), `capacity_pallets` (integer) | — |
| `carriers` | 8 | `id` (text), `name` (text), `service_level` (text) | — |
| `vehicle_types` | 8 | `id` (text), `name` (text), `max_payload_kg` (integer) | — |
| `drivers` | 8 | `id` (text), `full_name` (text), `license_class` (text) | — |
| `vehicles` | 8 | `id` (text), `carrier_id` (text), `vehicle_type_id` (text), `registration` (text), `payload_kg` (integer) | `carrier_id` → `carriers.id`, `vehicle_type_id` → `vehicle_types.id` |
| `addresses` | 8 | `id` (text), `customer_id` (text), `label` (text), `postal_code` (text) | `customer_id` → `customers.id` |
| `products` | 8 | `id` (text), `customer_id` (text), `sku` (text), `unit_weight_grams` (integer) | `customer_id` → `customers.id` |
| `inventory` | 8 | `id` (text), `warehouse_id` (text), `product_id` (text), `quantity` (integer) | `warehouse_id` → `warehouses.id`, `product_id` → `products.id` |
| `shipments` | 8 | `id` (text), `customer_id` (text), `origin_warehouse_id` (text), `destination_address_id` (text), `carrier_id` (text), `service` (text) | `customer_id` → `customers.id`, `origin_warehouse_id` → `warehouses.id`, `destination_address_id` → `addresses.id`, `carrier_id` → `carriers.id` |
| `shipment_items` | 8 | `id` (text), `shipment_id` (text), `product_id` (text), `quantity` (integer) | `shipment_id` → `shipments.id`, `product_id` → `products.id` |
| `routes` | 8 | `id` (text), `carrier_id` (text), `origin_warehouse_id` (text), `destination_warehouse_id` (text), `distance_km` (integer) | `carrier_id` → `carriers.id`, `origin_warehouse_id` → `warehouses.id`, `destination_warehouse_id` → `warehouses.id` |
| `trips` | 8 | `id` (text), `route_id` (text), `vehicle_id` (text), `driver_id` (text), `departure_date` (text) | `route_id` → `routes.id`, `vehicle_id` → `vehicles.id`, `driver_id` → `drivers.id` |
| `shipment_legs` | 8 | `id` (text), `shipment_id` (text), `trip_id` (text), `sequence` (integer) | `shipment_id` → `shipments.id`, `trip_id` → `trips.id` |
| `tracking_events` | 8 | `id` (text), `shipment_id` (text), `status` (text), `occurred_at` (text) | `shipment_id` → `shipments.id` |
| `delivery_attempts` | 8 | `id` (text), `shipment_id` (text), `driver_id` (text), `attempt_date` (text), `successful` (boolean) | `shipment_id` → `shipments.id`, `driver_id` → `drivers.id` |
| `invoices` | 8 | `id` (text), `customer_id` (text), `issued_date` (text), `total_cents` (integer) | `customer_id` → `customers.id` |
| `invoice_lines` | 8 | `id` (text), `invoice_id` (text), `shipment_id` (text), `charge_cents` (integer) | `invoice_id` → `invoices.id`, `shipment_id` → `shipments.id` |

The point-read and update target is `invoice_lines.charge_cents` where `id = 'invoice_lines_08'`. The aggregate sums `invoice_lines.charge_cents`. The transaction workload updates two existing rows atomically.

The relationship workload joins `shipments.customer_id` to `customers.id` and returns `[shipments.id, customers.name]` in child-ID order. SQL runs a native join; JayDB2 composes key enumeration and cell reads in the client.

The `jaydb2/` directory contains the actual configuration, empty application-table seed with a benchmark user, generic access, two-write, and six-cell row-read programs, and their universal certificates and termination proofs. The row-read program batches untimed full-data validation into one certified transaction per row; it is separate from the timed point-read and relationship workloads. Each project has eleven generated files: eight Bend sources, two SQL schemas, and this README. The runner inserts the canonical rows through admitted prepared requests; the seed file does not embed those rows. Relative Bend dependencies are supplied by the existing service staging path.

JayDB2 uses the permissive `Free` configuration: technical schema checks and authentication apply, but no administrator laws enforce foreign keys or domain invariants. The SQLite and PostgreSQL schemas declare real foreign-key constraints. SQLite additionally uses STRICT tables and Boolean checks; the runner enables `PRAGMA foreign_keys=ON`. These are explicit differences in integrity semantics.

Run this scenario on all three engines from the repository root:

```sh
experiments/database-comparison/run.sh \
  --scenarios 08_logistics --output build/comparison-08_logistics
```

Use a new output directory for each run. The runner owns the live databases and records correctness checks, setup costs, timings, storage, and restart behavior there. The source artifacts in this directory are generated for review.

Modeling limits:

- Money is integer BRL cents and weights use grams or kilograms as named. There is one representative stock item and shipment per customer. Inventory reservations, customs, vehicle capacity across combined loads, event history completeness, route optimization, and invoice reconciliation are outside this fixture.

Regenerate all projects after changing scenario definitions or the common adapters:

```sh
python3 -B experiments/database-comparison/materialize.py
python3 -B experiments/database-comparison/materialize.py --check
```
