#!/bin/sh
# Hold this once; bench.py and its build/check tools do not acquire nested locks.
set -eu
suite=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
exec flock /tmp/jaydb2-experiments-heavy.lock python3 -B "$suite/bench.py" "$@"
