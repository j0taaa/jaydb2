#!/usr/bin/env python3
"""Install the pinned compiler sources and an already built BendTT locally.

No global installation, dependency lookup or arbitrary kernel build occurs.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import tarfile
import tempfile
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
LOCK = json.loads((ROOT / 'tools/admission/toolchain.lock.json').read_text())


def check_sources(directory):
    for name, expected in LOCK['files'].items():
        if hashlib.sha256((directory / name).read_bytes()).hexdigest() != expected:
            raise RuntimeError('Toolchain source differs: ' + name)


def install(source=None, kernel=None):
    local = ROOT / '.tools'
    local.mkdir(exist_ok=True)
    target = local / ('bend-source-' + LOCK['version'])
    if target.exists():
        check_sources(target)
    else:
        with tempfile.TemporaryDirectory(dir=local, prefix='bootstrap-') as temp:
            stage = Path(temp)
            if source:
                source = source.resolve()
                check_sources(source)
            else:
                archive = stage / 'sources.tar.gz'
                with urllib.request.urlopen(LOCK['sourceUrl'], timeout=30) as incoming, archive.open('wb') as outgoing:
                    shutil.copyfileobj(incoming, outgoing)
                if hashlib.sha256(archive.read_bytes()).hexdigest() != LOCK['archiveSha256']:
                    raise RuntimeError('Official source archive differs from its pinned hash')
                with tarfile.open(archive) as tar:
                    tar.extractall(stage / 'unpacked', filter='data')
                source = stage / 'unpacked' / ('bend-' + LOCK['version'])
                check_sources(source)
            # Only the files needed by admission/emission; no mutable home cache.
            ready = stage / 'ready'
            for name in LOCK['files']:
                dst = ready / name
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source / name, dst)
            check_sources(ready)
            ready.rename(target)
    kernel_target = local / ('bendtt-' + LOCK['kernelSha256'])
    if not kernel_target.exists():
        if kernel is None:
            raise RuntimeError('Supply --kernel with the pinned, already-built Linux BendTT. No substitute kernel is accepted.')
        data = kernel.read_bytes()
        if hashlib.sha256(data).hexdigest() != LOCK['kernelSha256']:
            raise RuntimeError('BendTT differs from the pinned artifact')
        with tempfile.NamedTemporaryFile(dir=local, delete=False, prefix='kernel-') as f:
            temporary = Path(f.name)
            f.write(data)
        try:
            temporary.chmod(0o700)
            temporary.replace(kernel_target)
        finally:
            temporary.unlink(missing_ok=True)
    if hashlib.sha256(kernel_target.read_bytes()).hexdigest() != LOCK['kernelSha256']:
        raise RuntimeError('Local BendTT was modified')
    return target, kernel_target


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source', type=Path)
    p.add_argument('--kernel', type=Path)
    a = p.parse_args()
    sources, checker = install(a.source, a.kernel)
    print(json.dumps({'sourceDir': str(sources), 'kernelPath': str(checker)}))
