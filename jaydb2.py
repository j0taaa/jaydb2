#!/usr/bin/env python3
"""JayDB2 local integration runner (backend/proof work remains in progress)."""
import argparse
import os
from pathlib import Path
import sys

from tools.service.controller import Database
from tools.service.staging import Environment
from tools.service.loading import Runtime as LoadingRuntime
from tools.service.lifecycle import LifecycleRuntime
from tools.bootstrap import LOCK, ROOT


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--configuration', type=Path, required=True)
    p.add_argument('--seed', type=Path, required=True)
    p.add_argument('--bend-source', type=Path, default=os.environ.get('JAYDB_BEND_SOURCE', ROOT / '.tools' / ('bend-source-' + LOCK['version'])))
    p.add_argument('--bendtt', type=Path, default=os.environ.get('JAYDB_BENDTT', ROOT / '.tools' / ('bendtt-' + LOCK['kernelSha256'])))
    p.add_argument('--loading-runtime',type=Path,default=ROOT/'.tools/service/loading.so')
    p.add_argument('--lifecycle-runtime',type=Path,default=ROOT/'.tools/service/lifecycle.so')
    a = p.parse_args()
    if not a.bend_source.is_dir() or not a.bendtt.is_file():
        p.error('Instale a toolchain fixada com tools/bootstrap.py ou informe --bend-source e --bendtt')
    if not a.loading_runtime.is_file():
        p.error('Instale o loader com python3 -m tools.service.build_loading .tools/service/loading.so')
    if not a.lifecycle_runtime.is_file():
        p.error('Instale o runtime com python3 -m tools.service.build_lifecycle .tools/service/lifecycle.so')
    database = None
    try:
        loader=LoadingRuntime.load(a.loading_runtime)
        lifecycle=LifecycleRuntime.load(a.lifecycle_runtime,loading_runtime=loader)
        database = Database(Environment(a.configuration, a.seed), (a.bend_source.resolve(), a.bendtt.resolve()),
                            loading_runtime=loader,lifecycle_runtime=lifecycle)
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
