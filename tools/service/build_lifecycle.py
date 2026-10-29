"""Explicit offline build of the fixed NODELETE lifecycle DSO (never on request)."""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT/'tools/service'
COMPILER = Path('/usr/bin/clang-19')


def _digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def build(output):
    output = Path(output).absolute()
    output.parent.mkdir(parents=True, exist_ok=True)
    sources = [SOURCE/name for name in ('lifecycle.h', 'lifecycle.c', 'build_lifecycle.py')]
    source_hashes = {str(p.relative_to(ROOT) if p.is_relative_to(ROOT) else p.resolve()):
                     _digest(p) for p in sources}
    compiler_hash = _digest(COMPILER)
    arguments = [str(COMPILER), '--no-default-config', '-std=c11', '-O2', '-fPIC', '-fvisibility=hidden',
                 '-Wall', '-Wextra', '-Werror', '-shared', '-Wl,-z,now',
                 '-Wl,-z,defs', '-Wl,-z,nodelete', '-Wl,-Bsymbolic-functions',
                 str(SOURCE/'lifecycle.c')]
    inputs = {'abiVersion': 1, 'sources': source_hashes, 'compilerSha256': compiler_hash,
              'arguments': [*arguments, '-DJAYDB_LIFECYCLE_BUILD_ID="<buildIdentitySha256>"',
                            '-o', '<output>']}
    identity = hashlib.sha256(json.dumps(inputs, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    with tempfile.TemporaryDirectory(prefix='.jaydb-lifecycle-', dir=output.parent) as temporary:
        temporary = Path(temporary)
        binary = temporary/'lifecycle.so'
        subprocess.run([*arguments, '-DJAYDB_LIFECYCLE_BUILD_ID="'+identity+'"',
                        '-o', str(binary)], check=True)
        if any(_digest(p) != digest for p, digest in zip(sources, source_hashes.values())) or \
                _digest(COMPILER) != compiler_hash:
            raise RuntimeError('Lifecycle build inputs changed during compilation')
        manifest = {**inputs, 'buildIdentitySha256': identity, 'moduleSha256': _digest(binary),
                    'descriptorBytes': 112, 'processBytes': 104, 'receiptBytes': 16,
                    'spawnBytes': 24, 'finishBytes': 24, 'callBytes': 32, 'releaseBytes': 32,
                    'pointerBytes': 8, 'flags': 15, 'nodelete': True,
                    'baselineRetention': 'one fixed NODELETE lifecycle runtime per process',
                    'baselineAccounting': 'include actual retained backing; not a static memory witness',
                    'coreProfile': 'host establishes soft RLIMIT_CORE=0; hard is unchanged',
                    'childProfile': 'Linux/glibc setsid; no foreign reaper, SIGCHLD auto-reap, or session escape'}
        report = temporary/'lifecycle.json'
        report.write_text(json.dumps(manifest, indent=2)+'\n')
        os.replace(binary, output)
        os.replace(report, output.with_suffix(output.suffix+'.json'))
    return manifest


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    build(parser.parse_args().output)
