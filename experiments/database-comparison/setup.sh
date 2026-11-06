#!/bin/sh
# Ubuntu 24.04 x86-64: keep PostgreSQL and Python dependencies under build/.
set -eu
suite=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root=$(CDPATH= cd -- "$suite/../.." && pwd)
deps="$root/build/database-comparison-deps"
mkdir -p "$deps/archives"
cd "$deps/archives"
apt-get download postgresql-16=16.15-0ubuntu0.24.04.1 \
  postgresql-client-16=16.15-0ubuntu0.24.04.1 libpq5=16.15-0ubuntu0.24.04.1
for archive in ./*.deb; do
  dpkg-deb -x "$archive" "$deps"
done
uv venv --python python3 "$root/build/database-comparison-venv"
uv pip install --python "$root/build/database-comparison-venv/bin/python" 'psycopg[binary]==3.2.13'
