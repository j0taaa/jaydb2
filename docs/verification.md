# Local checks and CI

The checks use the ordinary project commands and unmodified pinned toolchain.
They do not replace proofs with mocks or alter server behavior.

## Every change: smoke

```sh
npm ci --prefix clients/typescript
npm ci --prefix clients/sql
bash tools/ci/check.sh smoke
```

This runs the TypeScript client's type checks and codec/transport tests, accessory
unit tests, all Rust host tests, strict Clippy and formatting. It needs Node 24, Rust/Cargo,
Python 3.12 and the installed pinned Bend tools: an existing host options test canonicalizes those installed paths. Clang
is not needed. Smoke does **not** execute the proof/native/recovery gates and
does not attest admission, durability or the application certificates. Standalone
client checks (`make test-client`) and SQL/Drizzle frontend checks
(`make test-sql`) need no Bend distribution.

The `Smoke` GitHub Actions workflow installs the actual pinned tools and runs
these same checks on pushes and pull requests. It does not create dummy tool
paths or skip the host option test. Actions are pinned to verified upstream
commit IDs, and the workflow has read-only repository permissions. Local smoke
runs use the tool installation from [INSTALL](../INSTALL.md).

## Before a release: complete validation

Install Clang 19 and the pinned Bend tools as described in [INSTALL](../INSTALL.md).
For a fresh installation, the following wraps the existing verified installer:

```sh
bash tools/ci/bootstrap.sh
# Or supply an already downloaded exact pinned kernel:
bash tools/ci/bootstrap.sh /path/to/bendtt
npm ci --prefix clients/typescript
npm ci --prefix clients/sql
bash tools/ci/check.sh full
```

Without an argument, bootstrap uses `gh` to download the existing `v0.1.0`
kernel distribution. Private-repository downloads require an authorized local
`gh` session, or the workflow's read-only `GH_TOKEN`. Existing SHA-256 checks
reject substituted sources and executables; no checker is rebuilt.

The complete path adds the general/contract/library/receipt proof aggregates in
both official modes, including the live worker refinement in `proof/Remote*.bend`.
It runs proof-negative controls, real native and service tests,
library applications, storage-fault and lost-response recovery tests, the web
demo, TypeScript real-service checks, the starter templates, and persistent task
usage. It also runs the live worker, migration, concurrency, offline storage
upgrade and power-loss suites and compares the store with the Bend reference.
The offline upgrade uses a legacy controller built from tag `thesis-2026` in a
separate cached worktree under `.build/release-legacy/`. Fetch that tag with
`git fetch origin tag thesis-2026` if it is absent. Real CUDA tests run separately
with `make test-gpu`.

The gate runs generated SQL certificates and real Drizzle CRUD/rollback/recovery
(`make test-sql-native`) and seeded SQL/Drizzle differential checks against
SQLite with real native workers (`make test-sql-stress`). The latter runs 600
randomized operations by default plus rollback, concurrency, authentication
and recovery controls. It requires a Linux session with unlimited hard stack. It can take a
substantial amount of time. A passing smoke run alone is insufficient for a
release.

`Full release checks` runs on version tags and can be started manually through
GitHub Actions. It installs the pinned tools into a fresh checkout. It validates
the selected revision; it does not publish a package, create a release, or deploy
anything.

## Live engine integration tests

Run the live worker, socket concurrency and online migration tests directly
after installing the pinned toolchain.

```sh
flock /tmp/jaydb2-experiments-heavy.lock bash -c '
  ulimit -s unlimited &&
  make build &&
  python3 -B -m unittest tests.live.test_remote_worker tests.live.test_concurrency tests.live.test_migration -v
'
```

These tests compare worker replies with the reference execution, exercise FIFO
and conflicting writes, and test cutover and recovery. The Rust host tests
exercise the store and WAL. The proof aggregate checks representable operation
exchanges under faithful host responses. Store, concurrency and durability
correctness remain trusted host duties. See the
[proof guide](../proof/README.md#trusted-base).

## Test lock and logs

Both check modes take `/tmp/jaydb2-experiments-heavy.lock` once. An externally
locked run must set `JAYDB_HEAVY_LOCK_FD` to the inherited descriptor holding
that lock, so the wrapper reuses its open file description; reopening the path
would deadlock. Individual `make` targets do not acquire the lock; when running
heavy targets directly, acquire it at the outermost command.
The wrapper creates a short private TMPDIR for Unix socket tests and removes it
afterward. GitHub's job logs contain command output; local runs report directly
to the terminal and can be captured with normal shell redirection.

Workflow files being present does not establish that GitHub-hosted jobs have
run. Local validation and hosted results are separate evidence.

Run checks from a frozen checkout;
editing a running shell script can invalidate the wrapper result even after its
child test command completes successfully.
