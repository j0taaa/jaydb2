"""Actual administrator-only elapsed timing; no quota policy."""
import json
from pathlib import Path
import tempfile
import unittest

from tests.service.test_end_to_end import ROOT, Server
from tools.client import frame, unframe


class TimingTests(unittest.TestCase):
    def server(self, folder, stderr=False, storage=None):
        temporary = tempfile.TemporaryDirectory(prefix='jaydb-timing-')
        self.addCleanup(temporary.cleanup)
        log = Path(temporary.name)/'timing.ndjson'
        options = ['--timing-log', '-' if stderr else str(log)]
        if storage:
            path, mode = storage
            options += ['--storage', str(path), '--storage-mode', mode]
        server = Server(folder, threads=1, options=options,
                        seed=not storage or storage[1] != 'open')
        self.addCleanup(server.close)
        return server, log

    def receipts(self, log):
        return [json.loads(line) for line in log.read_text().splitlines()]

    def test_timing_is_admin_only_and_preserves_source_and_argument_binding(self):
        folder = ROOT/'examples/access'
        server, log = self.server(folder)
        code, proof = ((folder/name).read_text() for name in ('Client.bend', 'ClientProof.bend'))
        self.assertEqual(server.call(code, proof, 'alice-token', 'fresh-token'),
                         {'status': 'success', 'value': 'fresh-token'})
        self.assertEqual(server.call(code, proof, 'alice-token'),
                         {'status': 'authentication', 'value': None})
        forged = code.replace('D.ReadCell{D.Users{}, id, "credential"}',
                              'D.ReadCell{D.Users{}, "bob", "credential"}')
        self.assertNotEqual(forged, code)
        self.assertEqual(server.call(forged, proof, 'fresh-token', 'forged'),
                         {'status': 'certificate', 'value': None})
        self.assertEqual(server.call(code, proof, 'fresh-token'),
                         {'status': 'refusal', 'value': 'cancelled'})
        self.assertEqual(server.exchange(frame(None)), {'status': 'input', 'value': None})
        server.finish()
        records = self.receipts(log)
        self.assertEqual([r['sequence'] for r in records], [1, 2, 3, 4, 5])
        self.assertEqual([r['principal'] for r in records], ['alice', None, 'alice', 'alice', None])
        self.assertTrue(all(int(r['elapsed_ns']) > 0 for r in records))
        self.assertTrue(all('quota' not in r and 'outcome' not in r for r in records))

    def test_queued_credential_exchange_uses_fresh_identity(self):
        folder = ROOT/'examples/credential-exchange'
        server, log = self.server(folder)
        code, proof = ((folder/name).read_text() for name in ('Client.bend', 'ClientProof.bend'))
        who, who_proof = ((folder/name).read_text() for name in ('Who.bend', 'WhoProof.bend'))
        incoming = frame(dict(code=code, proof=proof, credential='alice-token', arguments=None))
        incoming += frame(dict(code=who, proof=who_proof, credential='alice-token', arguments=None))
        server.process.stdin.write(incoming)
        server.process.stdin.flush()
        self.assertEqual(server.exchange(b''), {'status': 'success', 'value': 'bob-token'})
        self.assertEqual(server.exchange(b''), {'status': 'success', 'value': 'bob'})
        server.finish()
        self.assertEqual([r['principal'] for r in self.receipts(log)], ['alice', 'bob'])

    def test_durable_publication_and_same_binary_reopen(self):
        from tests.service.test_persistence import state_bytes
        with tempfile.TemporaryDirectory(prefix='jaydb-timing-durable-') as temporary:
            storage = Path(temporary)/'db'
            folder = ROOT/'examples/access'
            code, proof = ((folder/name).read_text() for name in ('Client.bend', 'ClientProof.bend'))
            server, log = self.server(folder, storage=(storage, 'create'))
            self.assertEqual(server.call(code, proof, 'alice-token', 'durable-new'),
                             {'status': 'success', 'value': 'durable-new'})
            self.assertEqual(self.receipts(log)[0]['principal'], 'alice')
            self.assertIn(b'durable-new', state_bytes(storage))
            self.assertNotIn(b'alice-token', state_bytes(storage))
            server.finish()
            reopened, new_log = self.server(folder, storage=(storage, 'open'))
            self.assertEqual(reopened.call(code, proof, 'durable-new'),
                             {'status': 'refusal', 'value': 'cancelled'})
            self.assertEqual(reopened.call(code, proof, 'alice-token'),
                             {'status': 'authentication', 'value': None})
            reopened.finish()
            self.assertEqual([r['sequence'] for r in self.receipts(new_log)], [1, 2])
            self.assertEqual([r['principal'] for r in self.receipts(new_log)], ['alice', None])

    def test_stderr_log_and_terminal_framing_are_outside_service(self):
        server, _ = self.server(ROOT/'examples/access', stderr=True)
        self.assertEqual(server.exchange(frame(None)), {'status': 'input', 'value': None})
        server.process.stdin.write(b'\x00')
        server.process.stdin.flush()
        server.process.stdin.close()
        header = server.read(8)
        self.assertEqual(unframe(header + server.read(int.from_bytes(header, 'big'))),
                         {'status': 'input', 'value': None})
        self.assertEqual(server.process.wait(timeout=30), 0)
        records = [json.loads(line) for line in server.diagnostics().splitlines() if line.startswith('{')]
        self.assertEqual(len(records), 1)
        self.assertIsNone(records[0]['principal'])
