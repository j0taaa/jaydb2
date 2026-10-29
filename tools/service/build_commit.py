"""Build the bounded publication primitive for the private completion hook.

The production critical body has no calls: only inline raw syscalls, bounded
loops, comparisons and stores. The extent is derived from Clang stack usage;
the assembly entry consumes one return address on the explicit stack.
"""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / 'tools/service'
COMPILER = Path('/usr/bin/clang-19')


def build(output, *, test_fixture=None):
    output = Path(output)
    output.parent.mkdir(parents=True, exist_ok=True)
    # Installation work only. Consumers never compile a receipt shim when
    # opening/closing a request module.
    from tools.service.build_loading import build as build_loading
    loading_file=output.with_name(output.name+'.loading.so')
    loading_manifest=build_loading(loading_file)
    flags = ['--no-default-config', '-std=c11', '-O2', '-fPIC', '-fno-builtin', '-fno-stack-protector',
             '-fno-asynchronous-unwind-tables', '-Wall', '-Wextra', '-Werror']
    with tempfile.TemporaryDirectory(prefix='jaydb2-commit-build-') as tmp:
        tmp = Path(tmp)
        provisional = ['-DJAYDB_COMMIT_STACK_BYTES=4096',
                       '-DJAYDB_COMMIT_BUILD_ID="'+('0'*64)+'"']
        if test_fixture is not None:
            flags += ['-DJAYDB_COMMIT_TEST']
        subprocess.run([str(COMPILER), *flags, *provisional, '-fstack-usage', '-c',
                        str(SOURCE/'commit.c'), '-o', str(tmp/'commit.o')], check=True)
        usage = (tmp/'commit.su').read_text()
        frames = {}
        for line in usage.splitlines():
            name, size, kind = line.rsplit('\t', 2)
            if kind != 'static':
                raise RuntimeError('Publication code requires a static stack bound')
            frames[name.rsplit(':', 1)[-1]] = int(size)
        if 'critical' not in frames:
            raise RuntimeError('Missing critical body stack metadata')
        ir = tmp/'commit.ll'
        subprocess.run([str(COMPILER), *flags, *provisional, '-S', '-emit-llvm',
                        str(SOURCE/'commit.c'), '-o', str(ir)], check=True)
        body = re.search(r'define[^\n]*@critical\([^\n]*\).*?\n}', ir.read_text(), re.S)
        if body is None:
            raise RuntimeError('Missing critical function in LLVM IR')
        calls = re.findall(r'\bcall\b[^\n]*', body[0])
        unexpected = [call for call in calls if ' asm ' not in call
                      and '@llvm.lifetime.' not in call]
        if test_fixture is None and unexpected:
            raise RuntimeError('Production publication body is not a leaf: '+repr(unexpected))
        # Clang reports the entire frame, including any red-zone use. Reserve
        # an additional ABI red zone, alignment slack and assembly call return.
        # There is no budget-dependent fraction or maximum stack quota.
        bound = frames['critical'] + 128 + 16 + 8
        extent = ((bound + 4095)//4096)*4096
        arguments = [str(COMPILER), *flags, f'-DJAYDB_COMMIT_STACK_BYTES={extent}',
                     '-shared', '-Wl,-z,now', '-Wl,-z,defs']
        if test_fixture is None:
            arguments += ['-nostdlib']
        arguments += [str(SOURCE/'commit.c'), str(SOURCE/'commit.S')]
        if test_fixture is not None:
            arguments += [str(test_fixture)]
        sources = [SOURCE/name for name in ('commit.c','commit.h','commit.S','build_commit.py')]
        sources += [ROOT/'native/accounting'/name for name in ('counter.h','window.h','deadline.h')]
        if test_fixture is not None:
            sources.append(Path(test_fixture))
        source_hashes = {str(p.relative_to(ROOT) if p.is_relative_to(ROOT) else p.resolve()):
                         hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
        compiler_hash = hashlib.sha256(COMPILER.read_bytes()).hexdigest()
        build_identity = hashlib.sha256(json.dumps({'sources':source_hashes,
            'compiler':compiler_hash,'arguments':arguments,'stackBytes':extent,
            'testFixture':test_fixture is not None},sort_keys=True,separators=(',',':')).encode()).hexdigest()
        # Never truncate a previously mapped DSO. A concurrent load sees the
        # old or new binary; the report/hash/loaded descriptor must all agree.
        with tempfile.TemporaryDirectory(prefix='.jaydb-commit-',dir=output.parent) as publish:
            publish=Path(publish)
            binary=publish/'module.so'
            subprocess.run([*arguments, '-DJAYDB_COMMIT_BUILD_ID="'+build_identity+'"',
                            '-o', str(binary)], check=True)
            current = {str(p.relative_to(ROOT) if p.is_relative_to(ROOT) else p.resolve()):
                       hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
            if current!=source_hashes or hashlib.sha256(COMPILER.read_bytes()).hexdigest()!=compiler_hash:
                raise RuntimeError('Commit inputs changed during compilation')
            module_hash=hashlib.sha256(binary.read_bytes()).hexdigest()
            os.replace(binary,output)
        report = {
            'testFixture': test_fixture is not None,
            'stackBytes': extent,
            'criticalFrameBytes': frames['critical'],
            'criticalIsLeaf': not unexpected,
            'criticalFixedLoopsAndRawSyscallsOnly': test_fixture is None and not unexpected,
            'stackUsage': usage,
            'compilerSha256': compiler_hash,
            'compilerDriverFlags': ['--no-default-config'],
            'compilerDefaultConfiguration': False,
            'moduleSha256': module_hash,
            'buildIdentitySha256': build_identity,
            'sources': source_hashes,
            'fullExecutableContractProved': False,
            'integratedIntoController': False,
            'loading':{'file':loading_file.name,'manifest':loading_manifest},
        }
        with tempfile.NamedTemporaryFile(mode='w',prefix='.jaydb-commit-',dir=output.parent,
                                         delete=False) as record:
            record.write(json.dumps(report,indent=2)+'\n')
        os.replace(record.name,output.with_suffix(output.suffix+'.json'))
        return report


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('output', type=Path)
    build(parser.parse_args().output)
