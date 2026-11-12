"""Actual timing+durable fatal/rollback boundaries (fault build required)."""
import json
import os
from pathlib import Path
import shutil
import tempfile
import unittest

from tests.service.test_end_to_end import ROOT, Server
from tests.service.test_persistence import BINARY, state_bytes
from tools.client import frame, prepared_frame, unframe
from tests.service.test_prepared import universal_access_proof


class TimingPersistenceTests(unittest.TestCase):
    def test_failed_commits_log_once_and_uncertain_commits_stop_queued_dispatch(self):
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
            for point in ('after_file_sync', 'before_replace', 'after_replace', 'before_write', 'before_slot_write', 'during_slot_write',
                          'after_slot_write', 'before_data_sync', 'after_data_sync', 'after_publish'):
                with self.subTest(point=point):
                    storage, log = root/point, root/(point+'.ndjson')
                    shutil.copytree(base, storage)
                    token = 'new-token'
                    if point in ('after_file_sync', 'before_replace', 'after_replace'):
                        token += 'x'*5000
                    env = dict(os.environ, JAYDB_STORAGE_FAULT=point)
                    server = Server(folder, binary=BINARY, threads=1, seed=False, env=env,
                        arguments=['--storage', str(storage), '--storage-mode', 'open',
                                   '--timing-log', str(log)])
                    try:
                        setup_records = 0
                        if len(token) > 4096:
                            prepared = server.prepared(0, code, 'alice-token', proof=universal_access_proof(proof))
                            self.assertEqual(prepared['status'], 'prepared', server.diagnostics())
                            setup_records = 1
                            first = prepared_frame(1, prepared['value'], 'alice-token', token)
                            later = prepared_frame(1, prepared['value'], 'alice-token', token+'-later')
                        else:
                            first = frame(dict(code=code, proof=proof, credential='alice-token', arguments=token))
                            later = frame(dict(code=code, proof=proof, credential='alice-token', arguments=token+'-later'))
                        server.process.stdin.write(first+later)
                        server.process.stdin.close()
                        if point in ('before_write', 'after_file_sync'):
                            header = server.read(8)
                            self.assertEqual(unframe(header+server.read(int.from_bytes(header, 'big'))),
                                             {'status': 'failure', 'value': None})
                            header = server.read(8)
                            self.assertEqual(unframe(header+server.read(int.from_bytes(header, 'big'))),
                                             {'status': 'failure', 'value': None})
                        result = server.process.wait(timeout=180)
                        self.assertEqual(server.process.stdout.read(), b'', server.diagnostics())
                        records = [json.loads(line) for line in log.read_text().splitlines()][setup_records:]
                        first = records[0]
                        self.assertEqual(first['principal'], 'alice')
                        self.assertGreaterEqual(int(first['elapsed_ns']), 1_000_000)
                        if point in ('before_write', 'after_file_sync'):
                            self.assertEqual(result, 0, server.diagnostics())
                            self.assertIn('STORAGE_IO', server.diagnostics())
                            self.assertEqual(len(records), 2)
                            self.assertEqual(records[1]['principal'], 'alice')
                            self.assertIn(b'alice-token', state_bytes(storage))
                            self.assertNotIn(token.encode(), state_bytes(storage))
                        else:
                            self.assertNotEqual(result, 0)
                            self.assertIn('STORAGE_UNCERTAIN', server.diagnostics())
                            self.assertEqual(len(records), 1, 'fatal attempt double logged or queued request selected')
                            self.assertEqual(first['sequence'], 1+setup_records)
                            if point in ('before_replace', 'before_slot_write', 'during_slot_write'):
                                # Entering slot write/replacement is conservatively
                                # uncertain even before a visible complete record.
                                # No rollback acknowledgement is allowed.
                                self.assertIn(b'alice-token', state_bytes(storage))
                                self.assertNotIn(token.encode(), state_bytes(storage))
                            else:
                                self.assertIn(token.encode(), state_bytes(storage))
                    finally:
                        server.close()
