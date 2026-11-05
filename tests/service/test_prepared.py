"""Universal preparation and native reuse against the real access law."""
import os
from pathlib import Path
import shutil
import tempfile
import unittest

from tests.service.test_end_to_end import ROOT, Server
from tools.client import encode, prepared_frame


def universal_access_proof(proof):
    # The existing proof already derives safety for arbitrary ctx,args. Only
    # its final target specializes those values to one concrete request.
    return proof.replace('def B.certificate(s, valid, identity, n):',
        'def B.certificate(ctx, args, s, valid, identity, n):\n  +ctx = ctx\n  +args = args'
        ).replace('I.context()', 'ctx').replace('I.arguments()', 'args')


class PreparedTests(unittest.TestCase):
    def server(self, folder, env=None):
        server = Server(folder, env=env)
        self.addCleanup(server.close)
        return server

    def test_reuse_current_identity_state_and_sealed_native_without_admission(self):
        example = ROOT/'examples/access'
        code = (example/'Client.bend').read_text()
        proof = '\uFEFF' + universal_access_proof((example/'ClientProof.bend').read_text())
        with tempfile.TemporaryDirectory(prefix='jaydb-prepared-test-') as temporary:
            folder = Path(temporary)
            # Changing original inputs after preparation cannot change the
            # instance's frozen configuration/dependencies or compiled source.
            (folder/'Size.bend').write_text('import Base\ndef message() -> Nat:\n  32768n\n')
            (folder/'Configuration.bend').write_text('import ./Size.bend as Size\n' +
                (example/'Configuration.bend').read_text().replace('32768n, 65536n', 'Size.message(), 65536n'))
            (folder/'Seed.bend').write_bytes((example/'Seed.bend').read_bytes())
            (folder/'Client.bend').write_text(code)
            (folder/'ClientProof.bend').write_text(proof)
            # Causal gate: this is the real node until disabled. A later
            # ordinary request MUST fail at the same gate, while handle calls
            # continue with no attempt to enter the checker/compiler pipeline.
            node = folder/'node'
            node.write_text('#!/bin/sh\nprintf x >> "$JAYDB_TEST_NODE_LOG"\n'
                'if [ -f "$JAYDB_TEST_NODE_OFF" ]; then echo admission-disabled >&2; exit 91; fi\n'
                'exec "$JAYDB_TEST_NODE" "$@"\n')
            node.chmod(0o700)
            log, disabled = folder/'node-calls', folder/'disable-node'
            env = dict(os.environ, PATH=str(folder)+os.pathsep+os.environ['PATH'],
                JAYDB_TEST_NODE=shutil.which('node'), JAYDB_TEST_NODE_LOG=str(log),
                JAYDB_TEST_NODE_OFF=str(disabled))
            server = self.server(folder, env)
            receipt = server.prepared(0, code, 'alice-token', 'ignored-at-prepare', proof)
            self.assertEqual(receipt['status'], 'prepared', server.diagnostics())
            handle = receipt['value']
            self.assertRegex(handle, r'^[0-9a-f]{64}$')
            # Real official compilation succeeds; consuming an oversized Nat
            # later fails in the native child after its private write.
            failing = code.replace('S.Finish{value}',
                'S.Finish{D.VInt{0, U32.from_nat(Nat.mul(16777216n, 16777216n))}}')
            bad = server.prepared(0, failing, 'alice-token', proof=proof)
            self.assertEqual(bad['status'], 'prepared', server.diagnostics())
            baseline = log.read_bytes()
            disabled.touch()
            for name in ('Configuration.bend', 'Size.bend', 'Seed.bend', 'Client.bend', 'ClientProof.bend'):
                (folder/name).write_text('changed-original-input')

            self.assertEqual(server.prepared(1, handle, 'alice-token', 'alice-new'),
                {'status': 'success', 'value': 'alice-new'}, server.diagnostics())
            self.assertEqual(server.prepared(1, handle, 'bob-token', 'bob-new'),
                {'status': 'success', 'value': 'bob-new'}, server.diagnostics())
            self.assertEqual(server.prepared(1, handle, 'alice-token', 'stale'),
                {'status': 'authentication', 'value': None})
            self.assertEqual(server.prepared(1, handle, 'alice-new'),
                {'status': 'refusal', 'value': 'cancelled'})
            self.assertEqual(server.prepared(1, bad['value'], 'alice-new', 'never-published'),
                {'status': 'failure', 'value': None}, server.diagnostics())
            self.assertIn('a Nat past the largest immediate', server.diagnostics())
            self.assertEqual(server.prepared(1, handle, 'alice-new', 'alice-final'),
                {'status': 'success', 'value': 'alice-final'}, server.diagnostics())

            # Runtime, admitted source, and admitted dependency tampering all
            # fail before running a prepared action or publishing anything.
            private = next(Path(tempfile.gettempdir()).glob(f'jaydb2-{server.process.pid}-*'))
            self.assertFalse((private/'decode').exists(), 'redundant decoder was compiled')
            prepared = next(p for p in private.glob('request-*') if (p/'Client.bend').read_text() == code)
            self.assertIn('Prepared.resolve_analysis(', (prepared/'Main.bend').read_text())
            self.assertIn('Bindings.proof_source()', (prepared/'Main.bend').read_text())
            for source in prepared.rglob('*.bend'):
                self.assertNotIn('alice-token', source.read_text())
                self.assertNotIn('bob-token', source.read_text())
            self.assertFalse(list(private.rglob('Seed.bend')))
            for artifact in (next(prepared.glob('*.program')), prepared/'Client.bend', prepared/'Size.bend',
                             private/'runtime/tools/service/stage.mjs'):
                original = artifact.read_bytes()
                try:
                    artifact.write_bytes(original+b'\nchanged')
                    self.assertEqual(server.prepared(1, handle, 'alice-final', 'tampered'),
                        {'status': 'failure', 'value': None}, server.diagnostics())
                    self.assertIn('PREPARED_INTEGRITY', server.diagnostics())
                finally:
                    artifact.write_bytes(original)
            self.assertEqual(server.prepared(1, handle, 'alice-final', 'alice-final'),
                {'status': 'success', 'value': 'alice-final'})
            self.assertEqual(log.read_bytes(), baseline, 'prepared route entered node')
            self.assertEqual(server.call(code, (example/'ClientProof.bend').read_text(), 'alice-final'),
                {'status': 'failure', 'value': None})
            self.assertNotEqual(log.read_bytes(), baseline, 'causal admission gate was not reached')
            self.assertIn('admission-disabled', server.diagnostics())

            other = self.server(example)
            self.assertEqual(other.prepared(1, handle, 'alice-token', 'foreign'),
                {'status': 'failure', 'value': None})
            self.assertEqual(other.call(code, (example/'ClientProof.bend').read_text(), 'alice-token', 'other-new'),
                {'status': 'success', 'value': 'other-new'}, other.diagnostics())
            self.assertEqual(server.prepared(2, handle, 'invalid'), {'status': 'authentication', 'value': None})
            # Authentication wins over both unknown handles and bad proof
            # fields, while malformed envelopes still win over authentication.
            for operation in (0, 1, 2):
                self.assertEqual(server.prepared(operation, 'absent', 'invalid', proof='bad proof'),
                    {'status': 'authentication', 'value': None})
                malformed = bytes((7, operation)) + encode({'credential': 'invalid'})
                self.assertEqual(server.exchange(len(malformed).to_bytes(8, 'big')+malformed),
                    {'status': 'input', 'value': None})
            self.assertEqual(server.prepared(1, handle, 'alice-final', proof='replacement'),
                {'status': 'input', 'value': None})
            self.assertEqual(server.exchange((2).to_bytes(8, 'big')+bytes((7, 9))),
                {'status': 'input', 'value': None})
            self.assertEqual(server.prepared(2, handle, 'alice-final'), {'status': 'invalidated', 'value': None})
            self.assertEqual(server.prepared(1, handle, 'alice-final', 'forgotten'),
                {'status': 'failure', 'value': None})
            self.assertEqual(server.prepared(1, bad['value'], 'alice-final'),
                {'status': 'refusal', 'value': 'cancelled'})
            # The inner record alone fits exactly. Its two control bytes must
            # still trigger the host's terminal message-limit response.
            empty = prepared_frame(1, handle, 'alice-final', '')
            oversized = prepared_frame(1, handle, 'alice-final', 'x'*(32768-(len(empty)-10)))
            self.assertEqual(len(oversized)-8, 32770)
            self.assertEqual(server.exchange(oversized[:8]), {'status': 'limit', 'value': None})
            other.finish()
            server.finish()

    def test_preparation_requires_universal_proof_and_pure_capture_free_sources(self):
        folder = ROOT/'examples/access'
        code, concrete = ((folder/name).read_text() for name in ('Client.bend', 'ClientProof.bend'))
        proof = universal_access_proof(concrete)
        server = self.server(folder)
        cases = [
            (code, concrete, 'HOST_CAPTURE'),
            (code.replace('D.ReadCell{D.Users{}, id,', 'D.ReadCell{D.Users{}, "bob",'), proof, 'PRIMARY_CHECK'),
            ('import ./Instance.bend as Captured\n'+code+
                '\ndef capture() -> D.Context:\n  Captured.context()\n', proof, 'HOST_CAPTURE'),
            ('import ./Instance.bend as Captured\n'+code+
                '\ndef capture() -> D.Value:\n  Captured.arguments()\n', proof, 'HOST_CAPTURE'),
            ('import ./Absent.bend as Absent\n'+code, proof, 'DEPENDENCY'),
            (code+'\ndef foreign() -> Unit:\n  import "./foreign.c"\n', proof, 'FOREIGN'),
        ]
        for source, certificate, diagnostic in cases:
            with self.subTest(diagnostic=diagnostic):
                before = len(server.diagnostics())
                self.assertEqual(server.prepared(0, source, 'alice-token', proof=certificate),
                    {'status': 'certificate', 'value': None}, server.diagnostics())
                self.assertIn(diagnostic, server.diagnostics()[before:])
        # A failed preparation has never invoked the client or changed state.
        self.assertEqual(server.call(code, concrete, 'alice-token', 'ordinary-new'),
            {'status': 'success', 'value': 'ordinary-new'}, server.diagnostics())
        server.finish()

        with tempfile.TemporaryDirectory(prefix='jaydb-prepared-response-') as temporary:
            narrow = Path(temporary)
            (narrow/'Configuration.bend').write_text((folder/'Configuration.bend').read_text().replace(
                'S.Limits{32768n, 65536n, 32768n}', 'S.Limits{32768n, 65536n, 64n}'))
            (narrow/'Seed.bend').write_bytes((folder/'Seed.bend').read_bytes())
            small = self.server(narrow)
            refused = small.prepared(0, code, 'alice-token', proof=proof)
            self.assertEqual(refused, {'status': 'limit', 'value': None}, small.diagnostics())
            self.assertLessEqual(len(encode(refused)), 64)
            private = next(Path(tempfile.gettempdir()).glob(f'jaydb2-{small.process.pid}-*'))
            self.assertFalse(list(private.glob('request-*')), 'oversized receipt registered a worker')
            self.assertEqual(small.call(code, concrete, 'alice-token', 'x'),
                {'status': 'success', 'value': 'x'}, small.diagnostics())
            small.finish()


if __name__ == '__main__':
    unittest.main(verbosity=2)
