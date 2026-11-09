# Hotel operations and guest stays

A small hotel group coordinates rooms, reservations, guest charges, housekeeping, maintenance, and feedback across properties.

This project has 15 tables and 120 deterministic seed rows. The [canonical scenario](../../scenarios/07_hotel.json) contains the schema, literal rows, workload metadata, and domain limitations.

Book a room and rate plan, record payment and optional amenities, then assign room service and collect post-stay feedback.

| Table | Rows | Columns | References |
| --- | ---: | --- | --- |
| `properties` | 8 | `id` (text), `name` (text), `city` (text), `timezone` (text) | — |
| `room_types` | 8 | `id` (text), `property_id` (text), `name` (text), `base_nightly_cents` (integer) | `property_id` → `properties.id` |
| `rooms` | 8 | `id` (text), `room_type_id` (text), `room_number` (text), `floor` (integer) | `room_type_id` → `room_types.id` |
| `guests` | 8 | `id` (text), `full_name` (text), `email` (text), `loyalty_tier` (text) | — |
| `departments` | 8 | `id` (text), `property_id` (text), `name` (text), `monthly_budget_cents` (integer) | `property_id` → `properties.id` |
| `employees` | 8 | `id` (text), `department_id` (text), `full_name` (text), `hourly_rate_cents` (integer) | `department_id` → `departments.id` |
| `rate_plans` | 8 | `id` (text), `room_type_id` (text), `name` (text), `nightly_cents` (integer) | `room_type_id` → `room_types.id` |
| `reservations` | 8 | `id` (text), `guest_id` (text), `room_id` (text), `check_in` (text), `nights` (integer) | `guest_id` → `guests.id`, `room_id` → `rooms.id` |
| `reservation_rates` | 8 | `id` (text), `reservation_id` (text), `rate_plan_id` (text), `nightly_cents` (integer) | `reservation_id` → `reservations.id`, `rate_plan_id` → `rate_plans.id` |
| `payments` | 8 | `id` (text), `reservation_id` (text), `method` (text), `amount_cents` (integer) | `reservation_id` → `reservations.id` |
| `amenities` | 8 | `id` (text), `property_id` (text), `name` (text), `unit_price_cents` (integer) | `property_id` → `properties.id` |
| `reservation_amenities` | 8 | `id` (text), `reservation_id` (text), `amenity_id` (text), `quantity` (integer) | `reservation_id` → `reservations.id`, `amenity_id` → `amenities.id` |
| `housekeeping_tasks` | 8 | `id` (text), `room_id` (text), `employee_id` (text), `service_date` (text), `planned_minutes` (integer) | `room_id` → `rooms.id`, `employee_id` → `employees.id` |
| `maintenance_requests` | 8 | `id` (text), `room_id` (text), `reported_by` (text), `description` (text), `estimated_cost_cents` (integer) | `room_id` → `rooms.id`, `reported_by` → `employees.id` |
| `reviews` | 8 | `id` (text), `reservation_id` (text), `rating` (integer), `comment` (text) | `reservation_id` → `reservations.id` |

The point-read and update target is `payments.amount_cents` where `id = 'payments_08'`. The aggregate sums `payments.amount_cents`. The transaction workload updates two existing rows atomically.

The relationship workload joins `reservations.guest_id` to `guests.id` and returns `[reservations.id, guests.full_name]` in child-ID order. SQL runs a native join; JayDB2 composes key enumeration and cell reads in the client.

The `jaydb2/` directory contains the actual configuration, empty application-table seed with a benchmark user, generic access, two-write, and six-cell row-read programs, and their universal certificates and termination proofs. The row-read program batches untimed full-data validation into one certified transaction per row; it is separate from the timed point-read and relationship workloads. Each project has eleven generated files: eight Bend sources, two SQL schemas, and this README. The runner inserts the canonical rows through admitted prepared requests; the seed file does not embed those rows. Relative Bend dependencies are supplied by the existing service staging path.

JayDB2 uses the permissive `Free` configuration: technical schema checks and authentication apply, but no administrator laws enforce foreign keys or domain invariants. The SQLite and PostgreSQL schemas declare real foreign-key constraints. SQLite additionally uses STRICT tables and Boolean checks; the runner enables `PRAGMA foreign_keys=ON`. These are explicit differences in integrity semantics.

Run this scenario on all three engines from the repository root:

```sh
experiments/database-comparison/run.sh \
  --scenarios 07_hotel --output build/comparison-07_hotel
```

Use a new output directory for each run. The runner owns the live databases and records correctness checks, setup costs, timings, storage, and restart behavior there. The source artifacts in this directory are generated for review.

Modeling limits:

- Money is integer BRL cents; dates use ISO text. Room availability overlaps, refunds, tax, card processing, and staff scheduling need application logic or additional constraints. Each property has one representative room and only eight rows per table.

Regenerate all projects after changing scenario definitions or the common adapters:

```sh
python3 -B experiments/database-comparison/materialize.py
python3 -B experiments/database-comparison/materialize.py --check
```
