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
  # Fail on new application/client boundaries before the longer core aggregates.
  make build test-accessories-native verify-integration test test-library test-feature-integration test-recovery-integration test-demo-web
fi
