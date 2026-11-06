# Cohort based professional learning platform

A twelve-table learning platform links organizations, learners and instructors with course content, scheduled cohorts, enrollment, assignment submissions, grading and fee collection.

This project has 12 tables and 96 deterministic seed rows. The [canonical scenario](../../scenarios/06_learning_platform.json) contains the schema, literal rows, workload metadata, and domain limitations.

Read and correct assignment grades, total awarded points, and display enrollment rosters with learner names.

| Table | Rows | Columns | References |
| --- | ---: | --- | --- |
| `organizations` | 8 | `id` (text), `name` (text), `country_code` (text) | — |
| `learners` | 8 | `id` (text), `name` (text), `email` (text), `organization_id` (text) | `organization_id` → `organizations.id` |
| `instructors` | 8 | `id` (text), `name` (text), `organization_id` (text), `expertise` (text) | `organization_id` → `organizations.id` |
| `courses` | 8 | `id` (text), `title` (text), `instructor_id` (text), `fee_cents` (integer), `currency` (text) | `instructor_id` → `instructors.id` |
| `modules` | 8 | `id` (text), `course_id` (text), `title` (text), `position` (integer) | `course_id` → `courses.id` |
| `lessons` | 8 | `id` (text), `module_id` (text), `title` (text), `duration_minutes` (integer) | `module_id` → `modules.id` |
| `cohorts` | 8 | `id` (text), `course_id` (text), `name` (text), `starts_on` (text), `capacity` (integer) | `course_id` → `courses.id` |
| `enrollments` | 8 | `id` (text), `learner_id` (text), `cohort_id` (text), `enrolled_on` (text), `status` (text) | `learner_id` → `learners.id`, `cohort_id` → `cohorts.id` |
| `assignments` | 8 | `id` (text), `lesson_id` (text), `title` (text), `max_score` (integer), `due_on` (text) | `lesson_id` → `lessons.id` |
| `submissions` | 8 | `id` (text), `assignment_id` (text), `enrollment_id` (text), `submitted_at` (text), `artifact_name` (text) | `assignment_id` → `assignments.id`, `enrollment_id` → `enrollments.id` |
| `grades` | 8 | `id` (text), `submission_id` (text), `reviewer_id` (text), `score` (integer), `feedback` (text) | `submission_id` → `submissions.id`, `reviewer_id` → `instructors.id` |
| `payments` | 8 | `id` (text), `enrollment_id` (text), `amount_cents` (integer), `currency` (text), `status` (text) | `enrollment_id` → `enrollments.id` |

The point-read and update target is `grades.score` where `id = 'grade_helo'`. The aggregate sums `grades.score`. The transaction workload updates two existing rows atomically.

The relationship workload joins `enrollments.learner_id` to `learners.id` and returns `[enrollments.id, learners.name]` in child-ID order. SQL runs a native join; JayDB2 composes key enumeration and cell reads in the client.

The `jaydb2/` directory contains the actual configuration, empty application-table seed with a benchmark user, generic access, two-write, and six-cell row-read programs, and their universal certificates and termination proofs. The row-read program batches untimed full-data validation into one certified transaction per row; it is separate from the timed point-read and relationship workloads. Each project has eleven generated files: eight Bend sources, two SQL schemas, and this README. The runner inserts the canonical rows through admitted prepared requests; the seed file does not embed those rows. Relative Bend dependencies are supplied by the existing service staging path.

JayDB2 uses the permissive `Free` configuration: technical schema checks and authentication apply, but no administrator laws enforce foreign keys or domain invariants. The SQLite and PostgreSQL schemas declare real foreign-key constraints. SQLite additionally uses STRICT tables and Boolean checks; the runner enables `PRAGMA foreign_keys=ON`. These are explicit differences in integrity semantics.

Run this scenario on all three engines from the repository root:

```sh
experiments/database-comparison/run.sh \
  --scenarios 06_learning_platform --output build/comparison-06_learning_platform
```

Use a new output directory for each run. The runner owns the live databases and records correctness checks, setup costs, timings, storage, and restart behavior there. The source artifacts in this directory are generated for review.

Modeling limits:

- Scores and durations are integers; all course prices and payments are denominated in BRL cents regardless of organization location.
- The fixture has one content module, lesson and graded submission per course; the schema supports many but is intentionally a small correctness fixture.
- Cross-course consistency between assignments and enrollments, cohort capacity, grade ranges, fee reconciliation and tenant authorization require additional rules beyond the declared foreign keys.
- Dates are ISO text; artifact names identify synthetic submissions and do not point to real files.

Regenerate all projects after changing scenario definitions or the common adapters:

```sh
python3 -B experiments/database-comparison/materialize.py
python3 -B experiments/database-comparison/materialize.py --check
```
