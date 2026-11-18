"""Measure prepared point calls over a durable Unix listener."""
from argparse import ArgumentParser
from concurrent.futures import ThreadPoolExecutor
import os
from pathlib import Path
from statistics import mean, median
from tempfile import TemporaryDirectory
from threading import Barrier
from time import perf_counter

from tests.live.test_concurrency import APP, Listener, exchange, execute
from tests.service.test_end_to_end import Server


class BenchmarkListener(Listener):
    def __init__(self, root, binary):
        self.endpoint = root / 'db.sock'
        Server.__init__(self, APP, binary=binary, env=dict(os.environ, TMPDIR=str(root)),
                        arguments=['--listen', str(self.endpoint), '--concurrency', '16',
                                   '--storage', str(root / 'db'), '--storage-mode', 'create'])


def call(stream, request):
    reply = exchange(stream, request)
    if reply['status'] != 'success':
        raise RuntimeError(reply)


def latency(server, label, request, count):
    with server.session() as stream:
        for _ in range(30):
            call(stream, request)
        samples = []
        for _ in range(count):
            start = perf_counter()
            call(stream, request)
            samples.append((perf_counter() - start) * 1000)
    p95 = sorted(samples)[(95 * count - 1) // 100]
    print(f'{label}: median {median(samples):.3f} ms, mean {mean(samples):.3f} ms, '
          f'p95 {p95:.3f} ms (n={count})', flush=True)


def throughput(server, handle, count):
    ready = Barrier(17)
    start = Barrier(17)

    def lane(index):
        request = execute(handle, [f'lane-{chr(ord("a") + index)}'])
        with server.session() as stream:
            for _ in range(8):
                call(stream, request)
            ready.wait(timeout=180)
            start.wait(timeout=180)
            for _ in range(count):
                call(stream, request)

    with ThreadPoolExecutor(16) as pool:
        tasks = [pool.submit(lane, index) for index in range(16)]
        ready.wait(timeout=180)
        begin = perf_counter()
        start.wait(timeout=180)
        for task in tasks:
            task.result()
        elapsed = perf_counter() - begin
    print(f'16 durable writers: {16 * count / elapsed:.1f} updates/s '
          f'({16 * count} updates in {elapsed:.3f} s)', flush=True)


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path)
    parser.add_argument('--reads', type=int, default=2000)
    parser.add_argument('--writes', type=int, default=400)
    parser.add_argument('--per-writer', type=int, default=120)
    args = parser.parse_args()

    with TemporaryDirectory(prefix='jaydb-bench-', dir='/tmp') as folder:
        server = BenchmarkListener(Path(folder), args.binary)
        try:
            with server.session() as stream:
                handle = server.prepare(stream)
            latency(server, 'point read', execute(handle, 'counter'), args.reads)
            latency(server, 'durable update', execute(handle, ['counter']), args.writes)
            throughput(server, handle, args.per_writer)
        finally:
            server.close()


if __name__ == '__main__':
    main()
