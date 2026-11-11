#!/usr/bin/env python3
"""Opt-in native CPU/frequency diagnostics; run under the common heavy lock.

Not a headline benchmark: LD_PRELOAD adds observation overhead. The native
program and its input/output bytes are unchanged. See paper/README.md.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from paper.bench.run import BUILD, ROOT, metadata, operation, package, session, source
from paper.bench.fixtures import bulk_population
from tools.client import prepared_frame


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=BUILD/'diagnosis.json')
    parser.add_argument('--calls', type=int, default=30)
    args = parser.parse_args()
    if args.calls < 1:
        parser.error('--calls must be positive')
    BUILD.mkdir(parents=True, exist_ok=True)
    (BUILD/'tmp').mkdir(exist_ok=True)
    observer = BUILD/'worker-clock.so'
    subprocess.run(['clang-19', '-shared', '-fPIC', '-O2',
                    str(ROOT/'paper/bench/worker-clock.c'), '-o', str(observer)], check=True)
    data = dict(metadata=metadata(), diagnostic=True, records=[],
                observer='LD_PRELOAD constructor/destructor: native body wall/process CPU, CPU frequency and rusage; not benchmark samples')
    # Restore the environment for callers importing this module.
    previous = {key: os.environ.get(key) for key in ('LD_PRELOAD', 'JAYDB_WORKER_CLOCK')}
    try:
        for kind, count, persistent in (('read', 10, False), ('read', 100, False),
                                        ('read', 1000, False), ('read', 1105, False),
                                        ('read', 10, True), ('indexed', 10, False),
                                        ('voucher', 10, False)):
            name = f'diagnose-{kind}-{count}-{persistent}'
            folder = package(BUILD/name, kind, 0 if count > 100 else count)
            clocks = BUILD/(name+'.clocks.jsonl')
            clocks.unlink(missing_ok=True)
            os.environ.update(LD_PRELOAD=str(observer), JAYDB_WORKER_CLOCK=str(clocks))
            code, proof, universal = source(folder)
            with session(folder, name, persistent=persistent, timing=True) as s:
                handle, _ = s.prepare(code, universal)
                if count > 100:
                    population, certificate = bulk_population(proof)
                    population_handle, _ = s.prepare(population, certificate)
                    s.call(population, certificate, [f'k{i:06d}' for i in range(count)],
                           dict(status='success', value=count), handle=population_handle)
                    s.exchange(prepared_frame(2, population_handle, 'alice-token'),
                               dict(status='invalidated', value=None))
                clock_offset = clocks.stat().st_size
                # Mark the exact measured window for an enclosing strace.
                os.write(2, f'DIAG START {name} pid={s.p.pid}\n'.encode())
                rows = []
                for i in range(args.calls+1):
                    call_args, value = operation(kind, i)
                    if kind == 'read':
                        call_args = ['read', f'k{count-1:06d}']
                    rows.append(s.call(code, proof, call_args,
                                       dict(status='success', value=value), handle=handle))
                    if kind == 'voucher':
                        s.call(code, proof, ['retire', f'r{i:04d}'],
                               dict(status='success', value='retired'), handle=handle)
                os.write(2, f'DIAG END {name}\n'.encode())
            data['records'].append(dict(program=kind, rows=count if kind == 'read' else None, persistent=persistent,
                samples=rows[1:], warmup=rows[:1],
                native_clocks=[json.loads(line) for line in clocks.read_bytes()[clock_offset:].decode().splitlines()]))
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps(data, indent=2)+'\n')
            print(name, 'complete', flush=True)
    finally:
        for key, value in previous.items():
            if value is None:
                os.environ.pop(key, None)
            else:
                os.environ[key] = value


if __name__ == '__main__':
    main()
