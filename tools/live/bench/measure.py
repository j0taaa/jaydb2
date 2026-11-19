#!/usr/bin/env python3
"""Startup, fdatasync, worker CPU, and listener measurements for the live comparison.

Run each subcommand with the thesis fixed-clock wrapper and the heavy lock.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import sys
from tempfile import TemporaryDirectory
from threading import Barrier
import time

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT))

from paper.bench import run
from paper.bench.frequency import observe
from paper.bench.workloads import max_rows, populate


def utc():
    return time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())


def startup(baseline, data):
    """Fresh stdio service with the unmodified thesis readiness exchange."""
    live = run.ROOT
    main_first = [('main', baseline), ('live', live)]
    data['engines'] = {}
    for pair in range(5):
        for persistent in (False, True) if pair % 2 == 0 else (True, False):
            order = main_first if (pair + persistent) % 2 == 0 else main_first[::-1]
            for revision, root in order:
                # Session and metadata already take their paths from these globals.
                run.ROOT = root
                run.BUILD = root / '.build/paper-bench'
                (run.BUILD / 'tmp').mkdir(parents=True, exist_ok=True)
                if revision not in data['engines']:
                    data['engines'][revision] = run.metadata(5)
                name = f'startup-{pair + 1}-{persistent}'
                folder = run.package(run.BUILD / name, 'read', rows=10)
                started = time.perf_counter_ns()
                service = run.Session(folder, name, persistent=persistent)
                elapsed = time.perf_counter_ns() - started
                service.close()
                data['records'].append(dict(revision=revision, persistent=persistent,
                    pair=pair + 1, elapsed_ns=elapsed, readiness_checked=True, utc=utc()))
                print('startup', revision, persistent, pair + 1, flush=True)
    run.ROOT = live
    run.BUILD = live / '.build/paper-bench'


def fdatasync(data):
    """Overwrite initialized extents and time pwrite and fdatasync separately."""
    for repetition in range(3):
        for size in (256, 4096) if repetition % 2 == 0 else (4096, 256):
            with TemporaryDirectory(prefix='fdatasync-', dir=run.BUILD) as folder:
                path = Path(folder) / 'sync'
                fd = os.open(path, os.O_CREAT | os.O_EXCL | os.O_RDWR, 0o600)
                try:
                    capacity = 8 * 1024 * 1024
                    assert os.pwrite(fd, bytes(capacity), 0) == capacity
                    os.fdatasync(fd)
                    rows = []
                    for index in range(105):
                        payload = bytes([(index % 254) + 1]) * size
                        started = time.perf_counter_ns()
                        written = os.pwrite(fd, payload, index * size)
                        wrote = time.perf_counter_ns()
                        os.fdatasync(fd)
                        synced = time.perf_counter_ns()
                        assert written == size
                        rows.append(dict(iteration=index, pwrite_ns=wrote - started,
                                         fdatasync_ns=synced - wrote, total_ns=synced - started))
                    data['records'].append(dict(size_bytes=size, repetition=repetition + 1,
                        initialized_bytes=capacity, warmup=rows[:5], samples=rows[5:]))
                finally:
                    os.close(fd)


def task_paths(pid):
    return Path(f'/proc/{pid}/task').iterdir()


def cpu_time(pid):
    return sum(int((task / 'schedstat').read_text().split()[0]) for task in task_paths(pid))


def worker(data):
    """Measure live warm reads and CPU runtime of the persistent worker."""
    folder = run.package(run.BUILD / 'worker-probe', 'read', rows=0)
    code, proof, universal = run.source(folder)
    with run.session(folder, 'worker-probe', timing=True) as service:
        handle, data['registration'] = service.prepare(code, universal)
        for rows in (10, max_rows()):
            population = populate(service, code, proof, rows)
            args = ['read', f'k{rows - 1:06d}']
            reply = dict(status='success', value=0)
            for _ in range(30):
                service.call(code, proof, args, reply, handle=handle)
            parent = service.p.pid
            children = [int(pid) for task in task_paths(parent)
                        for pid in (task / 'children').read_text().split()]
            assert len(children) == 1, children
            child = children[0]
            for trial in range(5):
                started = time.perf_counter_ns()
                worker_before = cpu_time(child)
                host_before = cpu_time(parent)
                client_before = time.process_time_ns()
                samples = [service.call(code, proof, args, reply, handle=handle)
                           for _ in range(300)]
                client_ns = time.process_time_ns() - client_before
                host_ns = cpu_time(parent) - host_before
                worker_ns = cpu_time(child) - worker_before
                data['records'].append(dict(rows=rows, trial=trial + 1, samples=samples,
                    elapsed_ns=time.perf_counter_ns() - started, worker_cpu_ns=worker_ns,
                    host_cpu_ns=host_ns, client_cpu_ns=client_ns, worker_pid=child,
                    worker_exe=os.readlink(f'/proc/{child}/exe')))
            data.setdefault('populations', {})[rows] = population
            print('worker', rows, 'complete', flush=True)


def measure_rate(service, handle, operation, clients):
    from tests.live.test_concurrency import exchange, execute

    writes = operation == 'update'
    count = 256 if writes else 2000
    warmups = 8
    start_ns = 0

    def mark_start():
        nonlocal start_ns
        start_ns = time.perf_counter_ns()

    warm = Barrier(clients + 1, timeout=180)
    start = Barrier(clients + 1, action=mark_start, timeout=180)

    def lane(index):
        key = f'lane-{chr(ord("a") + index)}'
        read = execute(handle, key)
        message = execute(handle, [key]) if writes else read
        with service.session() as stream:
            initial = exchange(stream, read)
            assert initial['status'] == 'success' and type(initial['value']) is int, initial
            base = initial['value']
            for iteration in range(warmups):
                expected = base + (iteration + 1 if writes else 0)
                assert exchange(stream, message) == dict(status='success', value=expected)
            warm.wait()
            start.wait()
            samples = []
            for iteration in range(count):
                before = time.perf_counter_ns()
                reply = exchange(stream, message)
                ended = time.perf_counter_ns()
                expected = base + (warmups + iteration + 1 if writes else 0)
                assert reply == dict(status='success', value=expected), (operation, key, reply)
                samples.append(ended - before)
        return dict(key=key, initial=base, expected=expected, samples_ns=samples,
                    last_response_ns=ended)

    with ThreadPoolExecutor(max_workers=clients) as pool:
        tasks = [pool.submit(lane, index) for index in range(clients)]
        warm.wait()
        offset = service.timing.stat().st_size
        start.wait()
        lanes = [task.result() for task in tasks]
    elapsed = max(row['last_response_ns'] for row in lanes) - start_ns
    with service.timing.open('rb') as log:
        log.seek(offset)
        timing = [json.loads(line) for line in log]
    assert len(timing) == clients * count, (operation, clients, len(timing))
    assert all((row['wal_batch'] >= 1) if writes else (row['wal_batch'] == 0) for row in timing)
    with service.session() as stream:
        for row in lanes:
            state = exchange(stream, execute(handle, row['key']))
            assert state == dict(status='success', value=row['expected']), (row['key'], state)
            row['readback'] = state['value']
    return dict(operation=operation, clients=clients, calls_per_client=count, warmups=warmups,
                elapsed_ns=elapsed, started_ns=start_ns, lanes=lanes,
                ops_per_second=clients * count * 1e9 / elapsed,
                retries_and_wal_batch=[[row['retries'], row['wal_batch']] for row in timing])


def throughput(data):
    from tests.live.test_concurrency import APP, Listener
    from tests.service.test_end_to_end import Server

    class BenchmarkListener(Listener):
        def __init__(self, folder):
            self.endpoint = folder / 'db.sock'
            self.timing = folder / 'service.ndjson'
            Server.__init__(self, APP, threads=1, env=dict(os.environ, TMPDIR=str(folder)),
                            arguments=['--listen', str(self.endpoint), '--concurrency', '16',
                                       '--storage', str(folder / 'db'), '--storage-mode', 'create',
                                       '--timing-log', str(self.timing)])

    conditions = [('read', 1), ('update', 4), ('read', 16),
                  ('update', 1), ('read', 4), ('update', 16)]
    for repetition in range(5):
        with TemporaryDirectory(prefix='jaydb-live-rate-', dir='/tmp') as directory:
            server = BenchmarkListener(Path(directory))
            try:
                with server.session() as stream:
                    handle = server.prepare(stream)
                for operation, clients in conditions[repetition:] + conditions[:repetition]:
                    cell = measure_rate(server, handle, operation, clients)
                    data['records'].append(dict(cell, repetition=repetition + 1))
                    print('throughput', repetition + 1, operation, clients,
                          round(cell['ops_per_second']), flush=True)
            finally:
                server.close()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('experiment', choices=('startup', 'fdatasync', 'worker', 'throughput'))
    parser.add_argument('--baseline', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        parser.error(f'output already exists: {args.output}')
    if args.experiment == 'startup' and args.baseline is None:
        parser.error('startup requires --baseline')
    if 'JAYDB_BENCH_FREQUENCY_ORIGINAL' not in os.environ:
        parser.error('run inside the thesis fixed-clock wrapper')

    started = time.perf_counter()
    runner = dict(command=sys.argv, started_utc=utc(),
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    data = dict(experiment=args.experiment, runner=runner, metadata=run.metadata(5), records=[])
    if args.experiment == 'startup':
        startup(args.baseline.resolve(), data)
    else:
        globals()[args.experiment](data)
    runner.update(completed_utc=utc(), elapsed_wall_seconds=time.perf_counter() - started)
    data['end_frequency'] = observe()
    temp = args.output.with_suffix('.json.tmp')
    with temp.open('x') as out:
        json.dump(data, out, separators=(',', ':'), allow_nan=False)
        out.write('\n')
    temp.replace(args.output)


if __name__ == '__main__':
    main()
