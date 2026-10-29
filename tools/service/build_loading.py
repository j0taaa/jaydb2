"""Explicit, offline build of the process-lifetime loader receipt shim.

No runtime module imports this builder or compiles a DSO. The host can pair this
build with other installation work under its own original resource budget.
Binary/report publication uses rename; an existing mapped file is not truncated.
The compiled descriptor is checked at load, in addition to the on-disk SHA256.
These identities identify code; they do not certify memory measurement or laws.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / 'tools/service'
COMPILER = Path('/usr/bin/clang-19')


def _digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def build(output):
    """Return the manifest and atomically publish output and output+'.json'."""
    output = Path(output).resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    sources = [SOURCE/name for name in ('loading.h', 'loading.c', 'build_loading.py')]
    source_hashes = {str(p.relative_to(ROOT) if p.is_relative_to(ROOT) else p.resolve()):
                     _digest(p) for p in sources}
    compiler_hash = _digest(COMPILER)
    arguments = [str(COMPILER), '--no-default-config', '-std=c11', '-O2', '-fPIC', '-fvisibility=hidden',
                 '-Wall', '-Wextra', '-Werror', '-shared', '-Wl,-z,now',
                 '-Wl,-z,defs', '-Wl,-z,nodelete', '-Wl,-Bsymbolic-functions',
                 str(SOURCE/'loading.c'), '-ldl']
    identity_inputs = {'sources': source_hashes, 'compilerSha256': compiler_hash,
                       'arguments': [*arguments,
                                     '-DJAYDB_LOADING_BUILD_ID="<buildIdentitySha256>"',
                                     '-o', '<output>'], 'abiVersion': 1}
    identity = hashlib.sha256(json.dumps(identity_inputs, sort_keys=True,
        separators=(',', ':')).encode()).hexdigest()
    with tempfile.TemporaryDirectory(prefix='.jaydb-loading-', dir=output.parent) as temporary:
        temporary = Path(temporary)
        binary = temporary/'loading.so'
        subprocess.run([*arguments, '-DJAYDB_LOADING_BUILD_ID="'+identity+'"',
                        '-o', str(binary)], check=True)
        if any(_digest(p) != source_hashes[str(p.relative_to(ROOT) if p.is_relative_to(ROOT)
                                               else p.resolve())] for p in sources) or \
                _digest(COMPILER) != compiler_hash:
            raise RuntimeError('Loader build inputs changed during compilation')
        manifest = {**identity_inputs, 'buildIdentitySha256': identity,
                    'moduleSha256': _digest(binary), 'descriptorBytes': 96,
                    'openReceiptBytes': 24, 'closeReceiptBytes': 16,
                    'pointerBytes': 8, 'nodelete': True,
                    'baselineRetention': 'one fixed runtime per process until OS termination',
                    'baselineAccounting': 'host must include actual retained backing; no static witness'}
        report = temporary/'loading.json'
        report.write_text(json.dumps(manifest, indent=2)+'\n')
        os.replace(binary, output)
        os.replace(report, output.with_suffix(output.suffix+'.json'))
    return manifest


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    build(parser.parse_args().output)
