#!/usr/bin/env bash
# Install the existing pinned distribution; never build a replacement checker.
set -euo pipefail
root=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
if [[ $# -gt 1 ]]; then
  echo "Usage: tools/ci/bootstrap.sh [/path/to/pinned/bendtt]" >&2
  exit 2
fi
cd "$root"
if [[ $# == 1 ]]; then
  python3 -B tools/bootstrap.py --kernel "$1"
else
  archive_dir=$(mktemp -d /tmp/jaydb-bootstrap.XXXXXXXX)
  trap 'rm -rf -- "$archive_dir"' EXIT
  gh release download v0.1.0 --repo j0taaa/jaydb2 \
    --pattern bendtt-linux-x86_64.tar.gz --dir "$archive_dir"
  # Extract only data files; the existing installer verifies the exact kernel.
  python3 - "$archive_dir" <<'PY'
from pathlib import Path
import sys, tarfile
directory = Path(sys.argv[1])
with tarfile.open(directory / 'bendtt-linux-x86_64.tar.gz') as archive:
    archive.extractall(directory, filter='data')
PY
  python3 -B tools/bootstrap.py --kernel "$archive_dir/bendtt-linux-x86_64/bendtt"
fi
python3 -B tools/bend.py version
