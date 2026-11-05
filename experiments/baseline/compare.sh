#!/bin/sh
set -eu
suite=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
exec flock /tmp/jaydb2-experiments-heavy.lock python3 -B "$suite/compare.py" "$@"
