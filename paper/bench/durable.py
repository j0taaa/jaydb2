#!/usr/bin/env python3
"""Focused three-session durable update and IO measurements; caller holds heavy lock.

Run with fixed-clock.sh. Writes only the explicitly named new output directory.
The workload is E3/E5's prepared point update (10 rows), with checked readback.
"""
import argparse
import json
import os
from pathlib import Path
import statistics
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from paper.bench.run import BUILD, metadata, package, session, source


def main():
    p = argparse.ArgumentParser(__doc__)
    p.add_argument('output', type=Path)
    p.add_argument('--samples', type=int, default=100)
    p.add_argument('--sessions', type=int, default=3)
    p.add_argument('--io-only', action='store_true')
    p.add_argument('--trace-host', action='store_true', help='strace only the coordinator; never trace worker children')
    p.add_argument('--binary', type=Path, default=ROOT/'target/release/jaydb2')
    args = p.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    BUILD.mkdir(parents=True, exist_ok=True)
    (BUILD/'tmp').mkdir(exist_ok=True)
    result = dict(metadata=metadata(args.sessions), records=[], io=[])
    import hashlib
    result['metadata']['measured_binary'] = str(args.binary.resolve())
    result['metadata']['binary_sha256'] = hashlib.sha256(args.binary.read_bytes()).hexdigest()
    result['metadata']['trace_host'] = args.trace_host
    # Session's normal process launch, optionally wrapped by strace WITHOUT -f:
    # tracing thousands of worker syscalls distorts both wall and sync timings.
    original_popen = subprocess.Popen
    trace_number = 0
    def launch(command, *positional, **keywords):
        nonlocal trace_number
        if isinstance(command, list) and command[0] == str(ROOT/'jaydb2'):
            command = [str(args.binary.resolve()), *command[1:]]
            if args.trace_host:
                trace_number += 1
                command = ['strace', '-T', '-yy', '-e', 'trace=fsync,fdatasync,rename,write',
                    '-o', str(args.output.resolve()/f'host-{trace_number}.strace'), *command]
        return original_popen(command, *positional, **keywords)
    subprocess.Popen = launch
    # Independent IO probe: 4 KiB payload, warmup excluded, directory already durable.
    folder = args.output/'io'; folder.mkdir()
    directory = os.open(folder, os.O_RDONLY | os.O_DIRECTORY)
    for kind in ('replace', 'append', 'preallocated', 'existing'):
        path = folder/kind
        fd = os.open(path, os.O_RDWR | os.O_CREAT | os.O_EXCL, 0o600)
        if kind == 'preallocated': os.posix_fallocate(fd, 0, (args.samples+1)*4096)
        if kind == 'existing':
            os.write(fd, bytes((args.samples+1)*4096))
            os.lseek(fd, 0, os.SEEK_SET)
        os.fsync(fd); os.fsync(directory)
        for i in range(args.samples+1):
            if kind == 'replace':
                os.close(fd)
                fd = os.open(folder/'temp', os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
            start = time.perf_counter_ns(); os.write(fd, bytes([i % 256])*4096)
            wrote = time.perf_counter_ns()
            (os.fsync if kind == 'replace' else os.fdatasync)(fd)
            synced = time.perf_counter_ns()
            if kind == 'replace': os.rename(folder/'temp', path)
            renamed = time.perf_counter_ns()
            if kind == 'replace': os.fsync(directory)
            end = time.perf_counter_ns()
            if i: result['io'].append(dict(kind=kind, write_ns=wrote-start, sync_ns=synced-wrote,
                rename_ns=renamed-synced, directory_sync_ns=end-renamed, total_ns=end-start))
        os.close(fd)
    os.close(directory)
    (args.output/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    if args.io_only: return
    for sid in range(args.sessions):
        for persistent in ([False, True] if sid % 2 == 0 else [True, False]):
            name=f'durable-{args.output.name}-{sid}-{persistent}'
            folder=package(BUILD/name, 'read', 10)
            code,proof,universal=source(folder)
            with session(folder,name,persistent=persistent) as s:
                handle, registration=s.prepare(code,universal)
                samples=[]
                for i in range(args.samples+1):
                    row=s.call(code,proof,['update','k000009',i+1],dict(status='success',value=True),handle=handle)
                    s.call(code,proof,['read','k000009'],dict(status='success',value=i+1),handle=handle)
                    if i: samples.append(row)
                result['records'].append(dict(session=sid+1,persistent=persistent,samples=samples))
                print(sid+1,persistent,statistics.median(r['elapsed_ns'] for r in samples)/1e6,flush=True)
            (args.output/'results.json').write_text(json.dumps(result,indent=2)+'\n')

if __name__ == '__main__': main()
