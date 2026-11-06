# Editorial publishing desk

Authors and sections support published articles, moderated reader comments, and editorial revision history.

This project has 5 tables and 40 deterministic seed rows. The [canonical scenario](../../scenarios/03_editorial_blog.json) contains the schema, literal rows, workload metadata, and domain limitations.

Revise an article reading estimate, total reading time, and show each article with its author name.

| Table | Rows | Columns | References |
| --- | ---: | --- | --- |
| `authors` | 8 | `id` (text), `name` (text), `email` (text), `role` (text), `active` (boolean) | — |
| `sections` | 8 | `id` (text), `name` (text), `slug` (text), `display_order` (integer) | — |
| `posts` | 8 | `id` (text), `author_id` (text), `section_id` (text), `title` (text), `published_on` (text), `reading_minutes` (integer) | `author_id` → `authors.id`, `section_id` → `sections.id` |
| `comments` | 8 | `id` (text), `post_id` (text), `display_name` (text), `body` (text), `approved` (boolean), `created_on` (text) | `post_id` → `posts.id` |
| `revisions` | 8 | `id` (text), `post_id` (text), `editor_id` (text), `revision_number` (integer), `summary` (text), `revised_on` (text) | `post_id` → `posts.id`, `editor_id` → `authors.id` |

The point-read and update target is `posts.reading_minutes` where `id = 'post_008'`. The aggregate sums `posts.reading_minutes`. The transaction workload updates two existing rows atomically.

The relationship workload joins `posts.author_id` to `authors.id` and returns `[posts.id, authors.name]` in child-ID order. SQL runs a native join; JayDB2 composes key enumeration and cell reads in the client.

The `jaydb2/` directory contains the actual configuration, empty application-table seed with a benchmark user, generic access, two-write, and six-cell row-read programs, and their universal certificates and termination proofs. The row-read program batches untimed full-data validation into one certified transaction per row; it is separate from the timed point-read and relationship workloads. Each project has eleven generated files: eight Bend sources, two SQL schemas, and this README. The runner inserts the canonical rows through admitted prepared requests; the seed file does not embed those rows. Relative Bend dependencies are supplied by the existing service staging path.

JayDB2 uses the permissive `Free` configuration: technical schema checks and authentication apply, but no administrator laws enforce foreign keys or domain invariants. The SQLite and PostgreSQL schemas declare real foreign-key constraints. SQLite additionally uses STRICT tables and Boolean checks; the runner enables `PRAGMA foreign_keys=ON`. These are explicit differences in integrity semantics.

Run this scenario on all three engines from the repository root:

```sh
experiments/database-comparison/run.sh \
  --scenarios 03_editorial_blog --output build/comparison-03_editorial_blog
```

Use a new output directory for each run. The runner owns the live databases and records correctness checks, setup costs, timings, storage, and restart behavior there. The source artifacts in this directory are generated for review.

Modeling limits:

- Dates use ISO 8601 strings; article bodies are omitted to keep the fixture focused on relational structure.
- Revisions retain editorial summaries rather than complete content snapshots.
- Email uniqueness, role permissions, and moderation policies are application concerns beyond the declared type and reference constraints.
- Eight rows per table test schema feasibility and basic workflows, not a production publishing workload.

Regenerate all projects after changing scenario definitions or the common adapters:

```sh
python3 -B experiments/database-comparison/materialize.py
python3 -B experiments/database-comparison/materialize.py --check
```
