#!/usr/bin/env bash
# Caller holds /tmp/jaydb2-experiments-heavy.lock. No nested lock.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
mkdir -p "$root/.build/paper-bench"
recovery=$(mktemp -d "$root/.build/paper-bench/frequency-XXXXXX")
python3 -B "$root/paper/bench/frequency.py" capture "$recovery/original.json"
restore() {
    status=$?
    trap - EXIT INT TERM HUP
    if ! sudo -n python3 -B "$root/paper/bench/frequency.py" restore "$recovery/original.json" > "$recovery/restored.json"; then
        echo "CPU RESTORATION FAILED; recovery snapshot: $recovery/original.json" >&2
        exit 1
    fi
    echo "CPU settings restored and verified: $recovery/restored.json" >&2
    exit "$status"
}
trap restore EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
trap 'exit 129' HUP
sudo -n python3 -B "$root/paper/bench/frequency.py" apply "$recovery/original.json" > "$recovery/applied.json"
export JAYDB_BENCH_FREQUENCY_ORIGINAL="$recovery/original.json"
# Do not exec: this shell must remain alive to execute the restoration trap.
"$@"
