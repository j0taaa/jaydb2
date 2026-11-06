# Outpatient clinic scheduling and billing

A ten-table synthetic outpatient system connecting specialties, clinicians and rooms to appointments, clinical encounters, diagnosis coding, prescriptions and invoices.

This project has 10 tables and 80 deterministic seed rows. The [canonical scenario](../../scenarios/05_clinic.json) contains the schema, literal rows, workload metadata, and domain limitations.

Read and adjust a consultation invoice, total invoiced BRL cents, and resolve appointment schedules to clinician display names.

| Table | Rows | Columns | References |
| --- | ---: | --- | --- |
| `specialties` | 8 | `id` (text), `name` (text), `department` (text) | — |
| `clinicians` | 8 | `id` (text), `name` (text), `specialty_id` (text), `license_code` (text) | `specialty_id` → `specialties.id` |
| `patients` | 8 | `id` (text), `name` (text), `birth_date` (text), `email` (text) | — |
| `rooms` | 8 | `id` (text), `name` (text), `location` (text), `active` (boolean) | — |
| `diagnoses` | 8 | `id` (text), `code` (text), `description` (text) | — |
| `appointments` | 8 | `id` (text), `patient_id` (text), `clinician_id` (text), `room_id` (text), `starts_at` (text), `status` (text) | `patient_id` → `patients.id`, `clinician_id` → `clinicians.id`, `room_id` → `rooms.id` |
| `encounters` | 8 | `id` (text), `appointment_id` (text), `reason` (text), `closed_at` (text) | `appointment_id` → `appointments.id` |
| `encounter_diagnoses` | 8 | `id` (text), `encounter_id` (text), `diagnosis_id` (text), `primary` (boolean) | `encounter_id` → `encounters.id`, `diagnosis_id` → `diagnoses.id` |
| `prescriptions` | 8 | `id` (text), `encounter_id` (text), `medication` (text), `instructions` (text), `duration_days` (integer) | `encounter_id` → `encounters.id` |
| `invoices` | 8 | `id` (text), `encounter_id` (text), `amount_cents` (integer), `status` (text), `due_date` (text) | `encounter_id` → `encounters.id` |

The point-read and update target is `invoices.amount_cents` where `id = 'inv_08'`. The aggregate sums `invoices.amount_cents`. The transaction workload updates two existing rows atomically.

The relationship workload joins `appointments.clinician_id` to `clinicians.id` and returns `[appointments.id, clinicians.name]` in child-ID order. SQL runs a native join; JayDB2 composes key enumeration and cell reads in the client.

The `jaydb2/` directory contains the actual configuration, empty application-table seed with a benchmark user, generic access, two-write, and six-cell row-read programs, and their universal certificates and termination proofs. The row-read program batches untimed full-data validation into one certified transaction per row; it is separate from the timed point-read and relationship workloads. Each project has eleven generated files: eight Bend sources, two SQL schemas, and this README. The runner inserts the canonical rows through admitted prepared requests; the seed file does not embed those rows. Relative Bend dependencies are supplied by the existing service staging path.

JayDB2 uses the permissive `Free` configuration: technical schema checks and authentication apply, but no administrator laws enforce foreign keys or domain invariants. The SQLite and PostgreSQL schemas declare real foreign-key constraints. SQLite additionally uses STRICT tables and Boolean checks; the runner enables `PRAGMA foreign_keys=ON`. These are explicit differences in integrity semantics.

Run this scenario on all three engines from the repository root:

```sh
experiments/database-comparison/run.sh \
  --scenarios 05_clinic --output build/comparison-05_clinic
```

Use a new output directory for each run. The runner owns the live databases and records correctness checks, setup costs, timings, storage, and restart behavior there. The source artifacts in this directory are generated for review.

Modeling limits:

- All patients, clinicians, license identifiers and prescriptions are fabricated benchmark data, not clinical guidance or real health records.
- Dates and timestamps are ISO text; money is integer BRL cents. Diagnosis codes are strings rather than a validated terminology service.
- The model does not implement medical access control, consent, audit requirements, scheduling conflict checks, drug safety checks or insurance claims.
- Relationships have foreign-key metadata; appointment uniqueness and one-primary-diagnosis rules require additional constraints or application laws.

Regenerate all projects after changing scenario definitions or the common adapters:

```sh
python3 -B experiments/database-comparison/materialize.py
python3 -B experiments/database-comparison/materialize.py --check
```
