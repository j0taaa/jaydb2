#!/usr/bin/env bash
# Reuse the same open file description when called under an outer heavy lock.
set -euo pipefail
cd "$(dirname "$0")/../.."
if [[ -n ${JAYDB_HEAVY_LOCK_FD:-} ]]; then
  [[ $(readlink "/proc/self/fd/$JAYDB_HEAVY_LOCK_FD") == /tmp/jaydb2-experiments-heavy.lock ]]
  exec 9>&"$JAYDB_HEAVY_LOCK_FD"
else
  exec 9>/tmp/jaydb2-experiments-heavy.lock
fi
flock 9
export JAYDB_HEAVY_LOCK_FD=9
ulimit -s unlimited
# Use a short Unix-socket directory regardless of worktree path length.
gpu_tmp=$(mktemp -d /tmp/jaydb-gpu.XXXXXXXX)
trap 'rm -rf -- "$gpu_tmp"' EXIT
export TMPDIR="$gpu_tmp"
export PYTHONPATH="$PWD"
make build
case ${1:-test} in
  test) python3 -B -m unittest tests.service.test_gpu tests.service.test_simulation.SimulationGpuTests -v ;;
  benchmark) bash paper/bench/fixed-clock.sh python3 -B paper/bench/gpu_programs.py --output paper/evidence/gpu-programs.json ;;
  simulation) bash paper/bench/fixed-clock.sh python3 -B paper/bench/simulation.py --output paper/evidence/simulation.json ;;
  *) exit 2 ;;
esac
