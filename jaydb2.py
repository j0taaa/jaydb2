#!/usr/bin/env python3
"""JayDB2 local integration runner (backend/proof work remains in progress)."""
import argparse
import os
from pathlib import Path
import sys

from tools.service.controller import Database
from tools.service.staging import Environment
from tools.bootstrap import LOCK, ROOT


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--configuration', type=Path, required=True)
    p.add_argument('--seed', type=Path, required=True)
    p.add_argument('--bend-source', type=Path, default=os.environ.get('JAYDB_BEND_SOURCE', ROOT / '.tools' / ('bend-source-' + LOCK['version'])))
    p.add_argument('--bendtt', type=Path, default=os.environ.get('JAYDB_BENDTT', ROOT / '.tools' / ('bendtt-' + LOCK['kernelSha256'])))
    a = p.parse_args()
    if not a.bend_source.is_dir() or not a.bendtt.is_file():
        p.error('Instale a toolchain fixada com tools/bootstrap.py ou informe --bend-source e --bendtt')
    database = None
    try:
        database = Database(Environment(a.configuration, a.seed), (a.bend_source.resolve(), a.bendtt.resolve()))
        database.serve()
        return 0
    except (BrokenPipeError, KeyboardInterrupt):
        return 0
    except Exception as e:
        print(f'jaydb2: {e}', file=sys.stderr)
        return 1
    finally:
        if database:
            database.close()


if __name__ == '__main__':
    raise SystemExit(main())
