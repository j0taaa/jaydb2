"""Checked read admission and real native read execution; FIFO tests below."""
from pathlib import Path
import tempfile
import unittest

from tests.service.test_end_to_end import ROOT, Server

CODE = (ROOT/'experiments/concurrency/Read.bend').read_text()
PROOF = (ROOT/'experiments/concurrency/ReadProof.bend').read_text()


class ReadBatchTests(unittest.TestCase):
    def test_checked_read_preparation_and_native_failures(self):
        server = Server(ROOT/'examples/credentials')
        self.addCleanup(server.close)
        receipt = server.prepared(3, CODE, 'alice-token', proof=PROOF)
        self.assertEqual(receipt['status'], 'prepared', server.diagnostics())
        handle = receipt['value']
        self.assertEqual(server.prepared(1, handle, 'alice-token'),
                         {'status': 'success', 'value': 'alice-token'}, server.diagnostics())
        self.assertEqual(server.prepared(1, handle, 'bob-token', 100000),
                         {'status': 'success', 'value': 100000}, server.diagnostics())
        self.assertEqual(server.prepared(1, handle, 'invalid'),
                         {'status': 'authentication', 'value': None})
        self.assertEqual(server.prepared(1, handle, 'alice-token', True),
                         {'status': 'failure', 'value': None}, server.diagnostics())
        self.assertEqual(server.prepared(1, handle, 'alice-token'),
                         {'status': 'success', 'value': 'alice-token'})
        # A client flag with an ordinary universal certificate grants no lane.
        ordinary_proof = PROOF.replace('def B.read_only(ctx, args):\n  (2n, read_only(ctx, args))', '')
        self.assertEqual(server.prepared(3, CODE, 'alice-token', proof=ordinary_proof),
                         {'status': 'certificate', 'value': None}, server.diagnostics())
        ordinary = server.prepared(0, CODE, 'alice-token', proof=ordinary_proof)
        self.assertEqual(ordinary['status'], 'prepared', server.diagnostics())
        self.assertEqual(server.prepared(1, ordinary['value'], 'alice-token'),
                         {'status': 'success', 'value': 'alice-token'})
        self.assertEqual(server.prepared(2, handle, 'alice-token'),
                         {'status': 'invalidated', 'value': None})
        self.assertEqual(server.prepared(1, handle, 'alice-token'),
                         {'status': 'failure', 'value': None})
        server.finish()


if __name__ == '__main__':
    unittest.main(verbosity=2)
