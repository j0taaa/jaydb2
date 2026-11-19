#!/usr/bin/env bash
# One entry point for local and hosted checks; take the heavy-work lock once.
set -euo pipefail
root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
mode=${1:-smoke}
if [[ $# -gt 1 || ( "$mode" != smoke && "$mode" != full ) ]]; then
  echo "Usage: tools/ci/check.sh [smoke|full]" >&2
  exit 2
fi
cd "$root"
# Reuse the caller's locked open file description for externally locked
# make smoke/check-release runs; reopening the path would deadlock.
if [[ -n ${JAYDB_HEAVY_LOCK_FD:-} ]]; then
  [[ $(readlink "/proc/self/fd/$JAYDB_HEAVY_LOCK_FD") == /tmp/jaydb2-experiments-heavy.lock ]]
  exec 9>&"$JAYDB_HEAVY_LOCK_FD"
else
  exec 9>/tmp/jaydb2-experiments-heavy.lock
fi
flock 9
if [[ "$mode" == full ]]; then
  # The production launcher needs this too; do not replace the official runtime.
  ulimit -s unlimited
fi
# Keep Unix sockets below Linux's address-length limit, regardless of checkout.
check_tmp=$(mktemp -d /tmp/jaydb-check.XXXXXXXX)
trap 'rm -rf -- "$check_tmp"' EXIT
export TMPDIR="$check_tmp"
export BEND_NO_TELEMETRY=1
printf 'Checking %s at %s\n' "$mode" "$(git rev-parse HEAD)"
make test-accessories
cargo test --locked
cargo fmt --check
cargo clippy --locked --all-targets -- -D warnings
if [[ "$mode" == full ]]; then
  # The complete-image executable embeds its source checkout path at build time.
  if ! legacy_commit=$(git rev-parse --verify --quiet 'refs/tags/thesis-2026^{commit}'); then
    echo 'Please fetch tag thesis-2026 with git fetch origin tag thesis-2026.' >&2
    exit 1
  fi
  legacy="$root/.build/release-legacy/$legacy_commit"
  mkdir -p "$(dirname "$legacy")"
  if [[ ! -d $legacy ]]; then
    git worktree add --detach "$legacy" "$legacy_commit"
  fi
  if [[ ! -e $legacy/.tools ]]; then
    ln -s "$root/.tools" "$legacy/.tools"
  fi
  cargo build --locked --release --manifest-path "$legacy/Cargo.toml" --target-dir "$legacy/target"
  make build
  fault_target="$root/.build/integration/fault"
  cargo build --locked --release --features storage-fault-injection --target-dir "$fault_target"
  JAYDB_LEGACY_BINARY="$legacy/target/release/jaydb2" \
    JAYDB_POWER_LOSS_FAULT_BINARY="$fault_target/release/jaydb2" \
    JAYDB_POWER_LOSS_NORMAL_BINARY="$root/target/release/jaydb2" \
    python3 -B -m unittest -v \
    tests.live.test_remote_worker tests.live.test_migration tests.live.test_concurrency \
    tests.live.test_storage_upgrade tests.live.test_crash_power_loss
  python3 -B tools/live/store_reference.py
  # Fail on new application/client boundaries before the longer core aggregates.
  make test-accessories-native verify-integration test test-library test-feature-integration test-recovery-integration test-demo-web
fi
