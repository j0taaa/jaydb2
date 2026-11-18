"""Run certified point reads and writes through concurrent Unix sessions."""
from concurrent.futures import ThreadPoolExecutor
from contextlib import contextmanager
import json
import os
from pathlib import Path
import signal
import socket
import tempfile
from threading import Barrier, Lock
from time import monotonic, sleep
import unittest

from tests.service.test_end_to_end import ROOT, Server
from tools.client import frame, prepared_frame, unframe


APP = ROOT / 'tests/live/concurrency'
TOKEN = 'alice-token'
INITIAL_LEFT = 100000


def receive(stream):
    def exact(size):
        data = bytearray()
        while len(data) < size:
            part = stream.recv(size - len(data))
            if not part:
                raise EOFError('incomplete response')
            data.extend(part)
        return data

    header = exact(8)
    return unframe(header + exact(int.from_bytes(header, 'big')))


def exchange(stream, message):
    stream.sendall(message)
    return receive(stream)


class Listener(Server):
    def __init__(self, root, *, mode='create'):
        self.endpoint = root / f'{mode}.sock'
        self.timing = root / f'{mode}.ndjson'
        super().__init__(APP, seed=mode == 'create', env=dict(os.environ, TMPDIR=str(root)),
                         arguments=['--listen', str(self.endpoint), '--concurrency', '16',
                                    '--storage', str(root / 'db'), '--storage-mode', mode,
                                    '--timing-log', str(self.timing)])

    @contextmanager
    def session(self):
        with socket.socket(socket.AF_UNIX) as stream:
            stream.settimeout(180)
            deadline = monotonic() + 180
            while True:
                try:
                    stream.connect(str(self.endpoint))
                    break
                except (FileNotFoundError, ConnectionRefusedError):
                    if self.process.poll() is not None or monotonic() >= deadline:
                        raise AssertionError('socket did not open\n' + self.diagnostics())
                    sleep(0.025)
            yield stream

    def prepare(self, stream):
        receipt = exchange(stream, prepared_frame(
            0, (APP / 'Client.bend').read_text(), TOKEN,
            proof=(APP / 'PreparedProof.bend').read_text()))
        if receipt['status'] != 'prepared':
            raise AssertionError(f'{receipt}\n{self.diagnostics()}')
        return receipt['value']

    def records(self):
        return [json.loads(line) for line in self.timing.read_text().splitlines()]


def execute(handle, args):
    return prepared_frame(1, handle, TOKEN, args)


class ConcurrencyTests(unittest.TestCase):
    def setUp(self):
        root = tempfile.TemporaryDirectory(prefix='jaydb-conc-', dir='/tmp')
        self.addCleanup(root.cleanup)
        self.root = Path(root.name)
        self.server = self.start()

    def start(self, mode='create'):
        server = Listener(self.root, mode=mode)
        self.addCleanup(server.close)
        return server

    def concurrent(self, message, *, clients=12, per_client=24):
        barrier = Barrier(clients, timeout=30)

        def run(_):
            with self.server.session() as stream:
                barrier.wait()
                return [exchange(stream, message) for _ in range(per_client)]

        with ThreadPoolExecutor(clients) as workers:
            return [reply for replies in workers.map(run, range(clients)) for reply in replies]

    def test_read_only_fifo_lost_updates_and_transfers(self):
        with self.server.session() as stream:
            handle = self.server.prepare(stream)
            query = execute(handle, 'counter')
            increment = execute(handle, ['counter'])
            self.assertEqual(exchange(stream, query), {'status': 'success', 'value': 0})
            self.assertEqual(list((self.root / 'db').glob('segment-*')), [],
                             'read-only success wrote a WAL segment')

            # Both frames are already in flight when the first reply arrives.
            stream.sendall(increment + query)
            for _ in range(2):
                self.assertEqual(receive(stream), {'status': 'success', 'value': 1})

            results = self.concurrent(increment)
            self.assertTrue(all(reply['status'] == 'success' for reply in results), results)
            self.assertEqual(sorted(reply['value'] for reply in results),
                             list(range(2, len(results) + 2)))
            self.assertEqual(exchange(stream, query)['value'], 1 + len(results))

            before = len(self.server.records())
            transfers = self.concurrent(execute(handle, ['left', 'right']))
            self.assertEqual(transfers, [{'status': 'success', 'value': None}] * len(transfers))
            records = self.server.records()[before:]
            self.assertEqual(len(records), len(transfers))
            self.assertGreater(sum(record['retries'] for record in records), 0,
                               'transfers never exercised OCC retries')
            left = exchange(stream, execute(handle, 'left'))['value']
            right = exchange(stream, execute(handle, 'right'))['value']
            self.assertEqual((left, right), (INITIAL_LEFT - len(transfers), len(transfers)))
            self.assertEqual(left + right, INITIAL_LEFT)
            self.assertEqual(exchange(stream, prepared_frame(2, handle, TOKEN))['status'], 'invalidated')
            self.assertEqual(exchange(stream, query)['status'], 'failure')

            # Oversized input closes just this session with the pipe-mode frame.
            self.assertEqual(exchange(stream, (65537).to_bytes(8, 'big'))['status'], 'limit')
            self.assertEqual(stream.recv(1), b'')
        with self.server.session() as other:
            self.assertEqual(exchange(other, frame(None))['status'], 'input')
        self.check_direct_sessions()

    def check_direct_sessions(self):
        code = (APP / 'Client.bend').read_text()
        proof = (APP / 'PreparedProof.bend').read_text().replace(
            'def B.certificate(ctx, args, s, valid, identity, n):\n'
            '  +context = ctx\n  +arguments = args',
            'def B.certificate(s, valid, identity, n):\n'
            '  +context = I.context()\n  +arguments = I.arguments()')
        started = Barrier(2, timeout=30)

        def direct(key):
            with self.server.session() as stream:
                started.wait()
                return exchange(stream, frame(dict(code=code, proof=proof, credential=TOKEN,
                                                    arguments=[key])))

        with ThreadPoolExecutor(2) as workers:
            replies = list(workers.map(direct, ['lane-a', 'lane-b']))
        self.assertEqual(replies, [{'status': 'success', 'value': 1}] * 2,
                         self.server.diagnostics())

    def test_sigkill_during_durable_transfers(self):
        with self.server.session() as stream:
            handle = self.server.prepare(stream)
        message = execute(handle, ['left', 'right'])
        clients = 8
        barrier = Barrier(clients, timeout=30)
        lock = Lock()
        acknowledged = 0
        interrupted = 0

        def run(_):
            nonlocal acknowledged, interrupted
            with self.server.session() as stream:
                barrier.wait()
                while True:
                    try:
                        response = exchange(stream, message)
                    except (EOFError, BrokenPipeError, ConnectionResetError):
                        with lock:
                            interrupted += 1
                        return
                    self.assertEqual(response, {'status': 'success', 'value': None})
                    with lock:
                        acknowledged += 1
                        if acknowledged == 48:
                            self.server.process.kill()

        with ThreadPoolExecutor(clients) as workers:
            list(workers.map(run, range(clients)))
        self.assertEqual(self.server.process.wait(timeout=10), -signal.SIGKILL)
        self.assertGreaterEqual(acknowledged, 48)
        self.assertEqual(interrupted, clients)

        server = self.start('open')
        with server.session() as stream:
            handle = server.prepare(stream)
            left = exchange(stream, execute(handle, 'left'))['value']
            right = exchange(stream, execute(handle, 'right'))['value']
        self.assertEqual(left + right, INITIAL_LEFT, 'recovery exposed a partial transfer')
        self.assertGreaterEqual(right, acknowledged, 'recovery lost acknowledged transfers')
        self.assertLessEqual(right, acknowledged + clients, 'recovery repeated transfers')


if __name__ == '__main__':
    unittest.main()
