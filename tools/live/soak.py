#!/usr/bin/env python3
"""Live engine soak: python3 -m tools.live.soak --duration 1800 --binary PATH.

Two durable hosts run side by side, each with concurrent sessions:

* bank (tests/live/concurrency): transfers between ten accounts, so the total
  is conserved and sessions conflict, plus a private counter per session whose
  acknowledged increments must survive every restart.
* tasks (applications/tasks): inserts, updates and removes of one row per
  session with titles of up to 4000 characters, contended updates of a shared
  row, and full inventory checks. Its WAL rotates every few minutes, so
  checkpoints must keep reclaiming segments.

Each host also prepares, uses and invalidates a fresh handle on a timer.
Workloads pause for invariant checks every --check-interval seconds and every
--restart-interval seconds the whole process group is killed mid-load and
reopened from storage. A sampler records host and worker RSS, open
descriptors and storage size. The summary reports requests, restarts,
invariant checks and per-generation resource ranges.
"""

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from contextlib import contextmanager
import json
import os
from pathlib import Path
from random import Random
import resource
import signal
import socket
import tempfile
from threading import Event, Lock, Thread
from time import monotonic, sleep

from applications.tasks.app import prepare as prepare_tasks
from tests.live.test_concurrency import APP as BANK_APP, INITIAL_LEFT, TOKEN, exchange, execute
from tests.service.test_end_to_end import ROOT, Server
from tools.client import prepared_frame


DISCONNECT = (EOFError, BrokenPipeError, ConnectionResetError)
SHARED = 'shared'
MISSING = object()
print_lock = Lock()


def event(kind, **fields):
    with print_lock:
        print(json.dumps({'event': kind, **fields}), flush=True)


class Service(Server):
    def __init__(self, name, root, app, binary, mode, clients, generation):
        self.endpoint = root / f'{name}.sock'
        self.endpoint.unlink(missing_ok=True)
        self.storage = root / f'{name}-db'
        self.timing = root / f'{name}-timing-{generation}.ndjson'
        self.scratch = tempfile.TemporaryDirectory(prefix=f'{name}-host-', dir=root)
        super().__init__(
            app, binary=binary, seed=mode == 'create', threads=1,
            env=dict(os.environ, TMPDIR=self.scratch.name),
            arguments=['--listen', str(self.endpoint), '--concurrency', str(clients),
                       '--storage', str(self.storage), '--storage-mode', mode,
                       '--timing-log', str(self.timing)])

    @contextmanager
    def session(self):
        with socket.socket(socket.AF_UNIX) as stream:
            stream.settimeout(300)
            deadline = monotonic() + 300
            while True:
                try:
                    stream.connect(str(self.endpoint))
                    break
                except (FileNotFoundError, ConnectionRefusedError):
                    if self.process.poll() is not None or monotonic() >= deadline:
                        raise AssertionError('socket did not open\n' + self.diagnostics())
                    sleep(0.025)
            yield stream

    def kill(self):
        assert self.process.poll() is None, self.diagnostics()
        os.killpg(self.process.pid, signal.SIGKILL)
        assert self.process.wait(timeout=30) == -signal.SIGKILL

    def close(self):
        super().close()
        self.scratch.cleanup()


def call(stream, handle, args, stats):
    reply = exchange(stream, execute(handle, args))
    stats['requests'] += 1
    return reply


def success(stream, handle, args, stats):
    reply = call(stream, handle, args, stats)
    assert reply['status'] == 'success', (args, reply)
    return reply['value']


class Bank:
    name = 'bank'
    ACCOUNTS = ['left', 'right'] + [f'lane-{letter}' for letter in 'ijklmnop']

    def __init__(self, root, clients, seed):
        self.app = BANK_APP
        self.prepare_frame = prepared_frame(0, (BANK_APP / 'Client.bend').read_text(), TOKEN,
                                            proof=(BANK_APP / 'PreparedProof.bend').read_text())
        self.counters = [f'lane-{letter}' for letter in 'abcdefgh'[:clients]]
        self.expected = dict.fromkeys(self.counters, 0)
        self.pending = {}
        self.seed = seed

    def setup(self, stream, handle, stats):
        pass

    def client(self, index, server, handle, stopping, stats):
        random = Random(self.seed * 1000 + index + stats['generations'] * 100)
        key = self.counters[index]
        with server.session() as stream:
            while not stopping.is_set():
                choice = random.random()
                if choice < 0.5:
                    reply = call(stream, handle, random.sample(self.ACCOUNTS, 2), stats)
                    assert reply in ({'status': 'success', 'value': None},
                                     {'status': 'refusal', 'value': None}), reply
                    stats['transfers' if reply['status'] == 'success' else 'refused_transfers'] += 1
                elif choice < 0.8:
                    self.pending[key] = self.expected[key] + 1
                    assert success(stream, handle, [key], stats) == self.pending[key]
                    self.expected[key] = self.pending.pop(key)
                    stats['increments'] += 1
                else:
                    assert success(stream, handle, key, stats) == self.expected[key]
                    stats['reads'] += 1
                    stats['invariant_checks'] += 1

    def churn_request(self):
        return 'left'

    def verify(self, server, handle, stats):
        with server.session() as stream:
            for key in self.counters:
                actual = success(stream, handle, key, stats)
                if key in self.pending:
                    # An increment in flight at the kill may or may not be durable.
                    assert actual in (self.expected[key], self.pending.pop(key)), key
                    stats['unacknowledged_resolved'] += 1
                    self.expected[key] = actual
                assert actual == self.expected[key], ('acknowledged increment lost', key, actual)
            balances = [success(stream, handle, key, stats) for key in self.ACCOUNTS]
            assert sum(balances) == INITIAL_LEFT, ('total not conserved', balances)
        stats['invariant_checks'] += len(self.counters) + 1
        stats['sum_checks'] += 1


def row(key, title, done=False):
    return {'id': key, 'owner': 'alice', 'title': title, 'completed': done}


class Tasks:
    name = 'tasks'

    def __init__(self, root, clients, seed):
        self.app = root / 'tasks-app'
        self.app.mkdir()
        prepare_tasks(self.app)
        proof = (self.app / 'ClientProof.bend').read_text().replace(
            'def B.certificate(s, valid, identity, n):\n'
            '  certify(I.context(), I.arguments(), B.code(), s, valid, identity, n)',
            'def B.certificate(ctx, args, s, valid, identity, n):\n'
            '  certify(ctx, args, B.code(), s, valid, identity, n)')
        self.prepare_frame = prepared_frame(0, (self.app / 'Client.bend').read_text(), TOKEN, proof=proof)
        self.keys = [f'lane-{index}' for index in range(clients)]
        self.expected = dict.fromkeys(self.keys)
        self.pending = {}
        self.versions = Counter()
        self.seed = seed

    def setup(self, stream, handle, stats):
        assert success(stream, handle, ['save', SHARED, SHARED, True], stats) == SHARED

    def client(self, index, server, handle, stopping, stats):
        random = Random(self.seed * 1000 + index + stats['generations'] * 100)
        key = self.keys[index]
        with server.session() as stream:
            while not stopping.is_set():
                choice = random.randrange(10)
                if choice < 3:
                    assert success(stream, handle, ['view', key], stats) == self.expected[key]
                    stats['reads'] += 1
                    stats['invariant_checks'] += 1
                elif choice < 6:
                    assert success(stream, handle, ['conclude', SHARED], stats) == SHARED
                    stats['contended_updates'] += 1
                else:
                    if self.expected[key] is not None and choice == 6:
                        args, self.pending[key], kind = ['remove', key], None, 'removes'
                    else:
                        self.versions[key] += 1
                        # Long titles fill 8 MiB segments, so rotation and reclamation recur.
                        title = f'{key}-{self.versions[key]}-' + 'x' * random.randrange(4000)
                        done = bool(self.versions[key] % 2)
                        args, self.pending[key] = ['save', key, title, done], row(key, title, done)
                        kind = 'inserts' if self.expected[key] is None else 'updates'
                    assert success(stream, handle, args, stats) == key
                    self.expected[key] = self.pending.pop(key)
                    stats[kind] += 1

    def churn_request(self):
        return ['view', SHARED]

    def verify(self, server, handle, stats):
        with server.session() as stream:
            for key in self.keys:
                actual = success(stream, handle, ['view', key], stats)
                if key in self.pending:
                    assert actual in (self.expected[key], self.pending.pop(key)), key
                    stats['unacknowledged_resolved'] += 1
                    self.expected[key] = actual
                assert actual == self.expected[key], ('acknowledged write lost', key, actual)
            listed = success(stream, handle, ['list'], stats)
            assert listed == sorted([SHARED, *(key for key in self.keys if self.expected[key])]), listed
            assert success(stream, handle, ['view', SHARED], stats) == row(SHARED, SHARED, True)
        stats['invariant_checks'] += len(self.keys) + 2
        stats['inventory_checks'] += 1


def churn(server, workload, stopping, stats, interval):
    """Prepare a fresh handle, use it once and invalidate it."""
    with server.session() as stream:
        while not stopping.wait(interval):
            reply = exchange(stream, workload.prepare_frame)
            assert reply['status'] == 'prepared', reply
            stats['requests'] += 1
            stats['prepares'] += 1
            success(stream, reply['value'], workload.churn_request(), stats)
            reply = exchange(stream, prepared_frame(2, reply['value'], TOKEN))
            assert reply == {'status': 'invalidated', 'value': None}, reply
            stats['requests'] += 1
            stats['invalidates'] += 1


def resources(host, directory):
    totals = Counter()
    remaining = [host]
    while remaining:
        pid = remaining.pop()
        proc = Path('/proc') / str(pid)
        try:
            for thread in (proc / 'task').iterdir():
                try:
                    remaining.extend(map(int, (thread / 'children').read_text().split()))
                except FileNotFoundError:
                    pass
            # Persistent transaction workers; transient compilers are skipped.
            if pid != host and not os.readlink(proc / 'exe').endswith('.program'):
                continue
            pages = int((proc / 'statm').read_text().split()[1])
            fds = len(list((proc / 'fd').iterdir()))
        except (FileNotFoundError, ProcessLookupError):
            continue
        group = 'host' if pid == host else 'workers'
        totals[f'{group}_kib'] += pages * os.sysconf('SC_PAGE_SIZE') // 1024
        totals[f'{group}_fds'] += fds
        totals[f'{group}_count'] += 1
    for path in directory.iterdir():
        try:
            size = path.stat().st_size
        except FileNotFoundError:
            continue
        totals['storage_bytes'] += size
        for prefix in ('segment', 'checkpoint'):
            if path.name.startswith(prefix + '-'):
                totals[f'{prefix}s'] += 1
    return dict(totals)


class Driver:
    def __init__(self, workload, root, args):
        self.workload = workload
        self.root = root
        self.args = args
        self.stats = Counter()
        self.server = None
        self.samples = []  # (generation, sample)
        self.killing = False

    def timings(self, server):
        if not server.timing.exists():
            return
        for line in server.timing.read_bytes().splitlines(keepends=True):
            if line.endswith(b'\n'):
                record = json.loads(line)
                self.stats['conflict_retries'] += record.get('retries', 0)
                self.stats['durable_commits'] += record.get('wal_batch', 0) > 0

    def client(self, run, stopping):
        try:
            run()
        except DISCONNECT:
            if not self.killing:
                raise

    def run(self, deadline):
        args, workload, stats = self.args, self.workload, self.stats
        generation = 0
        while True:
            mode = 'open' if generation else 'create'
            server = Service(workload.name, self.root, workload.app, args.binary, mode,
                             args.clients + 1, generation)
            self.server, self.killing = server, False
            stats['generations'] = generation
            try:
                with server.session() as stream:
                    reply = exchange(stream, workload.prepare_frame)
                    assert reply['status'] == 'prepared', (reply, server.diagnostics())
                    handle = reply['value']
                    stats['requests'] += 1
                    stats['prepares'] += 1
                    if not generation:
                        workload.setup(stream, handle, stats)
                workload.verify(server, handle, stats)
                ends = min(deadline, monotonic() + args.restart_interval)
                crash = ends < deadline
                while True:
                    phase = min(ends, monotonic() + args.check_interval)
                    stopping = Event()
                    with ThreadPoolExecutor(args.clients + 1) as pool:
                        tasks = [pool.submit(self.client, lambda index=index: workload.client(
                            index, server, handle, stopping, stats), stopping)
                            for index in range(args.clients)]
                        tasks.append(pool.submit(self.client, lambda: churn(
                            server, workload, stopping, stats, args.churn_interval), stopping))
                        try:
                            while monotonic() < phase:
                                for task in tasks:
                                    if task.done():
                                        task.result()
                                        raise AssertionError('a session stopped early')
                                sleep(min(1, max(0, phase - monotonic())))
                        finally:
                            if phase >= ends and crash:
                                # Abrupt stop with requests in flight.
                                self.killing = True
                                server.kill()
                            stopping.set()
                        for task in tasks:
                            task.result()
                    if self.killing:
                        break
                    workload.verify(server, handle, stats)
                    if phase >= ends:
                        break
                self.timings(server)
                if not crash:
                    return
                generation += 1
                stats['restarts'] += 1
                event('restart', host=workload.name, generation=generation)
            except Exception:
                event('failure', host=workload.name, diagnostics=server.diagnostics()[-4000:])
                raise
            finally:
                server.close()


def sampler(drivers, started, stopping, interval):
    while not stopping.wait(interval):
        for driver in drivers:
            server = driver.server
            if server is None or server.process.poll() is not None or not server.storage.exists():
                continue
            sample = resources(server.process.pid, server.storage)
            generation = driver.stats['generations']
            driver.samples.append((generation, sample))
            event('sample', host=driver.workload.name, seconds=round(monotonic() - started),
                  generation=generation, **sample)


def ranges(samples):
    """Per generation: first and last sample after warm-up, and the maximum."""
    report = {}
    for generation in sorted({generation for generation, _ in samples}):
        values = [sample for number, sample in samples if number == generation]
        steady = values[1:] or values
        report[generation] = {key: [steady[0].get(key, 0), steady[-1].get(key, 0),
                                    max(sample.get(key, 0) for sample in values)]
                              for key in sorted({key for sample in values for key in sample})}
    return report


def run(root, args):
    workloads = [Bank(root, args.clients, args.seed), Tasks(root, args.clients, args.seed)]
    drivers = [Driver(workload, root, args) for workload in workloads]
    started = monotonic()
    deadline = started + args.duration
    stopping = Event()
    monitor = Thread(target=sampler, args=(drivers, started, stopping, args.sample_interval), daemon=True)
    monitor.start()
    errors = []

    def drive(driver):
        try:
            driver.run(deadline)
        except Exception as error:
            errors.append((driver.workload.name, repr(error)[:4000]))

    threads = [Thread(target=drive, args=(driver,)) for driver in drivers]
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join()
    stopping.set()
    monitor.join()
    summary = {'seconds': round(monotonic() - started), 'errors': errors}
    for driver in drivers:
        stats = dict(driver.stats)
        stats.pop('generations', None)
        summary[driver.workload.name] = {'stats': stats, 'resources': ranges(driver.samples)}
    summary['requests'] = sum(driver.stats['requests'] for driver in drivers)
    summary['restarts'] = sum(driver.stats['restarts'] for driver in drivers)
    summary['invariant_checks'] = sum(driver.stats['invariant_checks'] for driver in drivers)
    event('summary', **summary)
    return int(bool(errors))


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--duration', type=float, default=1800, help='Total wall time in seconds')
    parser.add_argument('--restart-interval', type=float, default=300)
    parser.add_argument('--check-interval', type=float, default=60)
    parser.add_argument('--sample-interval', type=float, default=10)
    parser.add_argument('--churn-interval', type=float, default=15)
    parser.add_argument('--clients', type=int, default=6)
    parser.add_argument('--seed', type=int, default=483619)
    parser.add_argument('--binary', type=Path, default=ROOT / 'target/release/jaydb2')
    args = parser.parse_args()
    if min(args.duration, args.restart_interval, args.check_interval, args.sample_interval,
           args.churn_interval) <= 0:
        parser.error('duration and intervals must be positive')
    if not 2 <= args.clients <= 8:
        parser.error('clients must be between 2 and 8')
    args.binary = args.binary.resolve()
    # The project's usual launcher applies the same stack setting for Bend.
    _, hard_limit = resource.getrlimit(resource.RLIMIT_STACK)
    resource.setrlimit(resource.RLIMIT_STACK, (hard_limit, hard_limit))
    with tempfile.TemporaryDirectory(prefix='jaydb-soak-', dir=os.environ.get('TMPDIR', '/tmp')) as workspace:
        return run(Path(workspace), args)


if __name__ == '__main__':
    raise SystemExit(main())
