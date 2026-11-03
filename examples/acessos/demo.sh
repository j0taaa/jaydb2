#!/usr/bin/env bash
# Aplicação CLI: duas pessoas trocam suas próprias credenciais no mesmo banco.
set -euo pipefail
cd -- "$(dirname -- "$0")/../.."

request() {
  python3 tools/client.py --codigo examples/acessos/Client.bend \
    --prova examples/acessos/ClientProof.bend --credencial "$1" --argumentos "$2"
}

{
  request alice-token '"alice-nova"'
  request alice-token 'null'
  request alice-nova 'null'
  request alice-nova '"alice-final"'
  request bob-token '"bob-nova"'
} | ./jaydb2 --configuration examples/acessos/Configuration.bend \
      --seed examples/acessos/Seed.bend \
  | python3 tools/client.py --decode
