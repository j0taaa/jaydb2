#!/usr/bin/env bash
# CLI application: two people change their own credentials in the same database.
set -euo pipefail
cd -- "$(dirname -- "$0")/../.."

request() {
  python3 tools/client.py --code examples/access/Client.bend \
    --proof examples/access/ClientProof.bend --credential "$1" --arguments "$2"
}

{
  request alice-token '"alice-new"'
  request alice-token 'null'
  request alice-new 'null'
  request alice-new '"alice-final"'
  request bob-token '"bob-new"'
} | ./jaydb2 --configuration examples/access/Configuration.bend \
      --seed examples/access/Seed.bend \
  | python3 tools/client.py --decode
