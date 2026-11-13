#!/usr/bin/env python3
"""Profile admitted prepared-worker entry; caller holds heavy lock + fixed clock.

Uses existing symbols in literal official C, never edits/recompiles that C.
Run repeated_diagnose.py first. The directory contains its saved artifacts and
canonical input packets. The scratch repeated-host binary must already exist.
"""
import argparse
import json
import re
import statistics
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def capture(directory, output, calls):
    worker = next((directory / 'artifacts-1105').glob('request*/*.program'))
    source = (worker.parent / 'checked.c').read_text()
    # Find the actual continuation that receives the checked entry's result.
    # A C function return is not a Bend computation-completion boundary.
    blocks = re.findall(r'WL_CASE\((FID_main_c\d+)\)(.*?)(?=\n#if|\Z)', source, re.S)
    continuations = [re.search(r'STK\(0\) = (FID_main_k\d+);', body)[1]
                     for _, body in blocks if 'WL_JMP(FID_entry)' in body]
    assert len(continuations) == 1, continuations
    done = continuations[0]
    output.mkdir(parents=True, exist_ok=True)
    script = output / 'entry.bt'
    script.write_text('BEGIN { printf("READY\\n"); }\n' + '\n'.join([
        f'uprobe:{worker}:WL_FID_entry {{ @entry[tid]=nsecs; }}',
        f'uprobe:{worker}:WL_{done} {{ printf("entry %d %llu\\n",pid,nsecs-@entry[tid]); }}',
        f'uprobe:{worker}:WL_FID_Dispatch_read_root {{ @root[tid]=nsecs; }}',
        f'uprobe:{worker}:WL_FID_Dispatch_received {{ printf("root %d %llu\\n",pid,nsecs-@root[tid]); }}',
        'END { clear(@entry); clear(@root); }',
    ]) + '\n')
    host = ROOT / '.build/paper-bench/repeated-host/target/release/repeated-host'
    result = dict(worker=str(worker), continuation=done, calls=calls, observations=[])
    for count in (10, 1105):
        for op in ('read', 'update'):
            trace = output / f'{op}-{count}.bpf.txt'
            with trace.open('w') as stream:
                tracer = subprocess.Popen(['sudo', '-n', 'bpftrace', '-B', 'line', str(script)], stdout=stream)
                try:
                    deadline = time.monotonic() + 30
                    while 'READY' not in trace.read_text():
                        if tracer.poll() is not None: raise RuntimeError('bpftrace exited before READY')
                        if time.monotonic() > deadline: raise TimeoutError('bpftrace readiness')
                        time.sleep(.02)
                    observation = subprocess.check_output([str(host), 'capture', str(worker),
                        str(directory / f'{op}-{count}.worker.in'), str(calls), '1'])
                    (output / f'{op}-{count}.host.json').write_bytes(observation)
                finally:
                    subprocess.run(['sudo', '-n', 'kill', '-INT', str(tracer.pid)], check=True)
                    tracer.wait(timeout=20)
            measured = {}
            for phase in ('entry', 'root'):
                values = [int(m[1]) for m in re.findall(r'^' + phase + r' (\d+) (\d+)$', trace.read_text(), re.M)]
                assert len(values) == calls + 1, (phase, len(values), calls)
                measured[phase] = values[1:]
            result['observations'].append(dict(rows=count, operation=op, samples_ns=measured,
                medians_ms={phase: statistics.median(values)/1e6 for phase, values in measured.items()}))
            print(count, op, result['observations'][-1]['medians_ms'], flush=True)
    (output / 'profile.json').write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--calls', type=int, default=30)
    args = parser.parse_args()
    if args.calls < 1: parser.error('--calls must be positive')
    capture(args.directory.resolve(), args.output.resolve(), args.calls)
