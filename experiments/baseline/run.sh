#!/bin/sh
# All build, admission/native integration and measurement work shares this lock.
set -eu
suite=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
exec flock /tmp/jaydb2-experiments-heavy.lock python3 -B "$suite/bench.py" "$@"
