#!/bin/sh
set -eu
suite=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root=$(CDPATH= cd -- "$suite/../.." && pwd)
python=${COMPARISON_PYTHON:-$root/build/database-comparison-venv/bin/python}
exec flock /tmp/jaydb2-experiments-heavy.lock "$python" -B "$suite/run.py" "$@"
