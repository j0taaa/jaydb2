# Local checks and CI

The checks use the ordinary project commands and unmodified pinned toolchain.
They do not replace proofs with mocks or alter server behavior.

## Every change: smoke

```sh
npm ci --prefix clients/typescript
bash tools/ci/check.sh smoke
```

This runs the TypeScript client's type checks and codec/transport tests, accessory
unit tests, Rust host tests, strict Clippy, formatting, and benchmark-harness
oracles. It needs Node 24, Rust/Cargo, and Python 3.12; no Bend distribution or
Clang is needed. It does **not** attest real admission, emitted native programs,
durability, or the application certificates.

The `Smoke` GitHub Actions workflow runs these same checks on pushes and pull
requests. Actions are pinned to verified upstream commit IDs, and the workflow
has read-only repository permissions.

## Before a release: complete validation

Install Clang 19 and the pinned Bend tools as described in [INSTALL](../INSTALL.md).
For a fresh installation, the following wraps the existing verified installer:

```sh
bash tools/ci/bootstrap.sh
# Or supply an already downloaded exact pinned kernel:
bash tools/ci/bootstrap.sh /path/to/bendtt
npm ci --prefix clients/typescript
bash tools/ci/check.sh full
```

Without an argument, bootstrap uses `gh` to download the existing `v0.1.0`
kernel distribution. Private-repository downloads require an authorized local
`gh` session, or the workflow's read-only `GH_TOKEN`. Existing SHA-256 checks
reject substituted sources and executables; no checker is rebuilt.

The complete path adds the general/contract/library/receipt proof aggregates in
both official modes, proof-negative controls, real native and service tests,
library applications, storage-fault and lost-response recovery tests, the web
demo, TypeScript real-service checks, the starter templates, and persistent task
usage. It requires a Linux session with unlimited hard stack. It can take a
substantial amount of time. A passing smoke run alone is insufficient for a
release.

`Full release checks` runs on version tags and can be started manually through
GitHub Actions. It installs the pinned tools into a fresh checkout. It validates
the selected revision; it does not publish a package, create a release, or deploy
anything.

Both check modes take `/tmp/jaydb2-experiments-heavy.lock` once. Do not wrap them
in another `flock` of that lock. Individual `make` targets do not acquire it;
when running heavy targets directly, acquire the lock at the outermost command.
The wrapper creates a short private TMPDIR for Unix socket tests and removes it
afterward. GitHub's job logs contain command output; local runs report directly
to the terminal and can be captured with normal shell redirection.

Workflow files being present does not establish that GitHub-hosted jobs have
run. Local validation and hosted results are separate evidence.
