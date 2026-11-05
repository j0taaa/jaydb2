#!/usr/bin/env bash
set -euo pipefail
suite_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo_dir=$(cd -- "$suite_dir/../../.." && pwd)
if [[ $# -gt 1 || ( $# -eq 1 && $1 != --smoke ) ]]; then
  echo 'Usage: run.sh [--smoke]' >&2
  exit 2
fi
export JAYDB_INDEX_BENCH_OUTPUT="${JAYDB_INDEX_BENCH_OUTPUT:-$repo_dir/build/library/index-benchmark-$(date -u +%Y%m%dT%H%M%S)-$$}"
exec flock /tmp/jaydb2-experiments-heavy.lock bash -euo pipefail -c '
  cd -- "$1"
  cargo build --locked --release
  python3 -B "$2/prepare.py"
  python3 -B tools/check.py --timeout 120 "$JAYDB_INDEX_BENCH_OUTPUT/stage/Check.bend" "$JAYDB_INDEX_BENCH_OUTPUT/batch-proof/Check.bend"
  if [[ "$3" == --smoke ]]; then
    python3 -u -B "$2/run.py" --rows 8 --samples 2 --warmups 0
    python3 -u -B "$2/run_batch.py" --rows 8 --samples 2 --warmups 0 --queries 1 4
  else
    python3 -u -B "$2/run.py" --rows 8 64 256 --wide
    python3 -u -B "$2/run_batch.py"
  fi
  python3 -B "$2/analyze.py"
  printf "Results: %s\n" "$JAYDB_INDEX_BENCH_OUTPUT"
' index-benchmark "$repo_dir" "$suite_dir" "${1:-full}"
