"""Build only the independent allocation accounting tools."""
from pathlib import Path
import hashlib
import json
import subprocess
import os
import tempfile

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / 'native/accounting'
DEFAULT_OUTPUT = ROOT / 'tests/accounting/.build'


def build(output=DEFAULT_OUTPUT, *, test_races=False, static_observer=True):
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    flags = ['-std=c11', '-O2', '-g', '-Wall', '-Wextra', '-Werror', '-pthread', '-Wl,-z,now']
    if test_races:
        flags.append('-DJAYACCT_TEST_RACES')
    compiler = '/usr/bin/clang-19'
    library = output / 'libjayacct.so'
    tracer = output / 'jayacct-trace'
    observer_flags = [*flags, *(['-static'] if static_observer else [])]
    files = ['counter.h', 'window.h', 'deadline.h', 'counter.c', 'trace.c', 'objects.inc.c', 'deadline.inc.c', 'stage_control.h', 'stage_runtime.c', 'stage.inc.c']
    source_hashes = {name: hashlib.sha256((SOURCE / name).read_bytes()).hexdigest() for name in files}
    with tempfile.TemporaryDirectory(prefix='.accounting-build-', dir=output) as temporary:
        staged = Path(temporary)
        subprocess.run([compiler, *flags, '-fPIC', '-shared', str(SOURCE / 'counter.c'), str(SOURCE / 'stage_runtime.c'), '-o', str(staged/library.name)], check=True)
        subprocess.run([compiler, *observer_flags, str(SOURCE / 'counter.c'), str(SOURCE / 'trace.c'), '-o', str(staged/tracer.name)], check=True)
        if source_hashes != {name: hashlib.sha256((SOURCE / name).read_bytes()).hexdigest() for name in files}:
            raise RuntimeError('Accounting source changed during build; no new artifact published')
        # Readers that already mapped either ELF keep its original inode. Never
        # truncate an ELF in use by another integration probe or service owner.
        os.replace(staged/library.name, library)
        os.replace(staged/tracer.name, tracer)
    link_inputs = {}
    for name in ('libc.a','libpthread.a','libgcc.a','libgcc_eh.a','crt1.o','crti.o','crtn.o','crtbeginT.o','crtend.o'):
        path = Path(subprocess.check_output([compiler, '--print-file-name='+name], text=True).strip())
        if path.is_file():
            link_inputs[str(path.resolve())] = hashlib.sha256(path.read_bytes()).hexdigest()
    manifest = json.dumps({
        'compiler': subprocess.check_output([compiler, '--version'], text=True).splitlines()[0],
        'flags': flags,
        'observer_flags': observer_flags,
        'link_inputs': link_inputs,
        'sources': source_hashes,
        'artifacts': {path.name: hashlib.sha256(path.read_bytes()).hexdigest() for path in (library, tracer)},
    }, indent=2) + '\n'
    with tempfile.NamedTemporaryFile(mode='w', prefix='.accounting-manifest-', dir=output, delete=False) as stream:
        stream.write(manifest)
        name = stream.name
    os.replace(name, output/'BUILD.json')
    return library, tracer


if __name__ == '__main__':
    build()
