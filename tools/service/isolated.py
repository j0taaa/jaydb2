"""Explicit Python startup for the selected trusted service entrypoints.

This constructs argv only. Request helpers use a synchronous subprocess owner;
no resource observer is required. The source directory and Python installation
still need the environment's immutable-file contract.
"""
from pathlib import Path


PYTHON = '/usr/bin/python3'
ENTRIES = {
    'service': 'jaydb2.py',
    'admission': 'tools/admission/run.py',
    'native_simple': 'tools/native/build_simple.py',
}

# No input argument is inserted into executable Python text. Isolated mode
# removes cwd/user-site/environment path additions before this code runs;
# no-site additionally suppresses system .pth/sitecustomize initialization.
# The one project path is the host's frozen runtime, after stdlib paths.
BOOTSTRAP = '''import sys
if not (sys.flags.isolated and sys.flags.no_site and sys.flags.ignore_environment
        and sys.flags.safe_path and sys.flags.dont_write_bytecode):
    raise RuntimeError('The selected entry requires isolated Python startup')
root = sys.argv.pop(1)
sys.path.append(root)
sys.argv = [root + '/' + sys.argv[1], *sys.argv[2:]]
import runpy
runpy.run_path(sys.argv[0], run_name='__main__')
'''


def command(root, entry, arguments=()):
    """Return the fixed selected command, without changing env/fds/limits.

    root is supplied by the host, never by the submitted Bend program. The
    helper root is the tooling directory already materialized from immutable
    Environment bytes. An arbitrary pathname is not a trusted capsule merely
    because this function resolves it.
    """
    if entry not in ENTRIES:
        raise ValueError('Unknown trusted Python entrypoint')
    root = Path(root).resolve()
    return [PYTHON, '-I', '-S', '-B', '-c', BOOTSTRAP,
            str(root), ENTRIES[entry], *map(str, arguments)]
