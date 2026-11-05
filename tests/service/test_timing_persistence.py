"""Actual timing+quota+durable fatal/rollback boundaries (fault build required)."""
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest

from tests.service.test_end_to_end import ROOT, Server
from tests.service.test_persistence import BINARY, state_bytes
from tools.client import frame, unframe


class TimingPersistenceTests(unittest.TestCase):
    def test_failed_commits_charge_once_and_uncertain_commits_stop_queued_dispatch(self):
        self.assertTrue(BINARY.is_file(), 'Build the storage-fault-injection binary first')
        folder = ROOT/'examples/access'
        code, proof = ((folder/name).read_text() for name in ('Client.bend', 'ClientProof.bend'))
        with tempfile.TemporaryDirectory(prefix='jaydb-timing-fault-') as temporary:
            root = Path(temporary)
            base = root/'base'
            initial = Server(folder, binary=BINARY, threads=1,
                arguments=['--storage', str(base), '--storage-mode', 'create'])
            try:
                self.assertEqual(initial.call('', '', 'bad-token')['status'], 'authentication')
                initial.finish()
            finally:
                initial.close()
            for point in ('before_replace', 'after_replace', 'after_publish'):
                with self.subTest(point=point):
                    storage, log = root/point, root/(point+'.ndjson')
                    shutil.copytree(base, storage)
                    env = dict(os.environ, JAYDB_STORAGE_FAULT=point)
                    server = Server(folder, binary=BINARY, threads=1, seed=False, env=env,
                        arguments=['--storage', str(storage), '--storage-mode', 'open',
                                   '--timing-log', str(log), '--quota-period-ms', '86400000',
                                   '--quota-budget-ms', '1'])
                    try:
                        first = frame(dict(code=code, proof=proof, credential='alice-token', arguments='new-token'))
                        later = frame(dict(code=code, proof=proof, credential='alice-token', arguments='must-not-run'))
                        server.process.stdin.write(first+later)
                        server.process.stdin.close()
                        if point == 'before_replace':
                            header = server.read(8)
                            self.assertEqual(unframe(header+server.read(int.from_bytes(header, 'big'))),
                                             {'status': 'failure', 'value': None})
                            header = server.read(8)
                            self.assertEqual(unframe(header+server.read(int.from_bytes(header, 'big'))),
                                             {'status': 'quota', 'value': None})
                        result = server.process.wait(timeout=180)
                        self.assertEqual(server.process.stdout.read(), b'', server.diagnostics())
                        records = [json.loads(line) for line in log.read_text().splitlines()]
                        first = records[0]
                        self.assertEqual(first['principal'], 'alice')
                        self.assertEqual(first['quota']['used_ns'], first['elapsed_ns'])
                        self.assertGreaterEqual(int(first['elapsed_ns']), 1_000_000)
                        if point == 'before_replace':
                            self.assertEqual(result, 0, server.diagnostics())
                            self.assertEqual(len(records), 2)
                            self.assertEqual(records[1]['outcome'], 'quota')
                            self.assertIn(b'alice-token', state_bytes(storage))
                            self.assertNotIn(b'new-token', state_bytes(storage))
                        else:
                            self.assertNotEqual(result, 0)
                            self.assertIn('STORAGE_UNCERTAIN', server.diagnostics())
                            self.assertEqual(len(records), 1, 'fatal attempt double charged or queued request selected')
                            self.assertEqual(first['sequence'], 1)
                            self.assertIn(b'new-token', state_bytes(storage))
                    finally:
                        server.close()
