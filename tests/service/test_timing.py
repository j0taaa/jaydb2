"""Real authentication, source binding, policy receipts and administrator timing.

Run under the shared heavy lock, with worktree-local TMPDIR.
Deterministic period/overshoot accounting is covered by Rust Manual-clock tests.
"""
import json
from pathlib import Path
import tempfile
import unittest

from tests.service.test_end_to_end import ROOT, Server
from tools.client import frame


class TimingTests(unittest.TestCase):
    def server(self, folder, quota=False, stderr=False):
        temp = tempfile.TemporaryDirectory(prefix='jaydb-timing-test-')
        self.addCleanup(temp.cleanup)
        log = Path(temp.name)/'timing.ndjson'
        options = ['--threads', '1', '--timing-log', '-' if stderr else str(log)]
        if quota:
            # First real checker/compiler attempt easily exceeds 1ms. Assert
            # the actual measured charge before depending on exhaustion.
            options += ['--quota-period-ms', '86400000', '--quota-budget-ms', '1']
        server = Server(folder, options=options)
        self.addCleanup(server.close)
        return server, log

    def receipts(self, log):
        return [json.loads(line) for line in log.read_text().splitlines()]

    def test_timing_is_admin_only_and_preserves_source_and_argument_binding(self):
        folder = ROOT/'examples/access'
        server, log = self.server(folder)
        code, proof = ((folder/name).read_text() for name in ('Client.bend', 'ClientProof.bend'))
        response = {'status': 'success', 'value': 'fresh-token'}
        self.assertEqual(server.call(code, proof, 'alice-token', 'fresh-token'), response)
        # Old credential no longer authenticates; altered source cannot reuse
        # the prior certificate or the identity from that successful request.
        self.assertEqual(server.call(code, proof, 'alice-token'),
                         {'status': 'authentication', 'value': None})
        forged = code.replace('D.ReadCell{D.Users{}, id, "credential"}',
                              'D.ReadCell{D.Users{}, "bob", "credential"}')
        self.assertNotEqual(forged, code)
        self.assertEqual(server.call(forged, proof, 'fresh-token', 'forged'),
                         {'status': 'certificate', 'value': None})
        self.assertEqual(server.call(code, proof, 'fresh-token'),
                         {'status': 'refusal', 'value': 'cancelled'})
        # Complete malformed requests are selected/timed, but not charged.
        self.assertEqual(server.exchange(frame(None)), {'status': 'input', 'value': None})
        server.finish()  # Also rejects any extra timing bytes in client stdout.
        receipts = self.receipts(log)
        self.assertEqual([r['sequence'] for r in receipts], [1, 2, 3, 4, 5])
        self.assertEqual([r['principal'] for r in receipts], ['alice', None, 'alice', 'alice', None])
        self.assertTrue(all(r['outcome'] == 'ordinary' and r['quota'] is None for r in receipts))
        self.assertTrue(all(int(r['elapsed_ns']) > 0 for r in receipts))

    def test_completion_charge_tracks_actor_across_credential_exchange(self):
        folder = ROOT/'examples/credential-exchange'
        server, log = self.server(folder, quota=True)
        code, proof = ((folder/name).read_text() for name in ('Client.bend', 'ClientProof.bend'))
        who, who_proof = ((folder/name).read_text() for name in ('Who.bend', 'WhoProof.bend'))
        self.assertEqual(server.call(code, proof, 'alice-token'),
                         {'status': 'success', 'value': 'bob-token'})
        first = self.receipts(log)[0]
        self.assertEqual(first['principal'], 'alice')
        self.assertGreaterEqual(int(first['quota']['used_ns']), 1_000_000)
        # Same credential now belongs to bob, who has an independent quota.
        self.assertEqual(server.call(who, who_proof, 'alice-token'),
                         {'status': 'success', 'value': 'bob'})
        # The other credential now identifies exhausted alice. Invalid source
        # must not reach admission; this is explicitly a host policy receipt.
        self.assertEqual(server.call('invalid source', '', 'bob-token'),
                         {'status': 'quota', 'value': None})
        self.assertEqual(server.call(code, proof, 'bad-token'),
                         {'status': 'authentication', 'value': None})
        # Denied invalidation must not inspect/mutate the handle registry.
        self.assertEqual(server.prepared(2, 'unknown-handle', 'bob-token'),
                         {'status': 'quota', 'value': None})
        server.finish()
        receipts = self.receipts(log)
        self.assertEqual([r['principal'] for r in receipts], ['alice', 'bob', 'alice', None, 'alice'])
        self.assertEqual(receipts[2]['outcome'], 'quota')
        self.assertEqual(receipts[2]['quota']['used_ns'], str(int(first['elapsed_ns']) + int(receipts[2]['elapsed_ns'])))
        self.assertIsNone(receipts[3]['quota'])

    def test_authenticated_failure_is_charged_and_restart_resets(self):
        folder = ROOT/'examples/access'
        server, log = self.server(folder, quota=True)
        code = (folder/'Client.bend').read_text()
        # Exact invalid proof/source attempt still authenticates and is charged.
        self.assertEqual(server.call(code, '', 'alice-token'),
                         {'status': 'certificate', 'value': None})
        receipt = self.receipts(log)[0]
        self.assertGreaterEqual(int(receipt['quota']['used_ns']), 1_000_000)
        self.assertEqual(server.call(code, '', 'alice-token'),
                         {'status': 'quota', 'value': None})
        # A genuinely checked program can fail inside the official runtime;
        # that completed authenticated attempt is also charged exactly once.
        proof = (folder/'ClientProof.bend').read_text()
        failing = code.replace('S.Finish{value}',
            'S.Finish{D.VInt{0, U32.from_nat(Nat.mul(16777216n, 16777216n))}}')
        self.assertNotEqual(failing, code)
        self.assertEqual(server.call(failing, proof, 'bob-token', 'not-published'),
                         {'status': 'failure', 'value': None}, server.diagnostics())
        failure = self.receipts(log)[2]
        self.assertEqual(failure['principal'], 'bob')
        self.assertEqual(failure['quota']['used_ns'], failure['elapsed_ns'])
        self.assertEqual(server.call(code, proof, 'bob-token'),
                         {'status': 'quota', 'value': None})
        server.finish()
        restarted, new_log = self.server(folder, quota=True)
        self.assertEqual(restarted.call(code, '', 'alice-token'),
                         {'status': 'certificate', 'value': None})
        restarted.finish()
        self.assertEqual(self.receipts(new_log)[0]['outcome'], 'ordinary')

    def test_stderr_log_and_terminal_framing_are_outside_service(self):
        server, _ = self.server(ROOT/'examples/access', stderr=True)
        self.assertEqual(server.exchange(frame(None)), {'status': 'input', 'value': None})
        server.process.stdin.write(b'\x00')
        server.process.stdin.flush()
        server.process.stdin.close()
        from tools.client import unframe
        header = server.read(8)
        self.assertEqual(unframe(header + server.read(int.from_bytes(header, 'big'))),
                         {'status': 'input', 'value': None})
        self.assertEqual(server.process.wait(timeout=30), 0)
        receipts = [json.loads(line) for line in server.diagnostics().splitlines() if line.startswith('{')]
        self.assertEqual(len(receipts), 1)  # Only the complete frame was selected.
        self.assertIsNone(receipts[0]['principal'])
