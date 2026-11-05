"""Real FIFO CLI/pinned native workers. Run under the shared heavy lock."""
import os
from pathlib import Path
import shutil
import tempfile
import unittest

from tests.service.test_end_to_end import ROOT, Server
from tests.service.test_prepared import universal_access_proof
from tools.client import frame, prepared_frame, unframe


class SchedulingTests(unittest.TestCase):
    def server(self, env=None):
        server = Server(ROOT/'examples/access', env=env, threads=1)
        self.addCleanup(server.close)
        return server

    def receive(self, server):
        header = server.read(8)
        return unframe(header + server.read(int.from_bytes(header, 'big')))

    def ordinary(self, credential, arguments=None):
        folder = ROOT/'examples/access'
        return frame(dict(code=(folder/'Client.bend').read_text(),
                          proof=(folder/'ClientProof.bend').read_text(),
                          credential=credential, arguments=arguments))

    def test_pipelined_ordinary_and_prepared_controls_use_successive_current_snapshots(self):
        server = self.server()
        incoming = [self.ordinary('alice-token', 'alice-new'), frame(None),
                    self.ordinary('alice-token'), self.ordinary('alice-new'),
                    self.ordinary('bob-token', 'bob-new')]
        server.process.stdin.write(b''.join(incoming))
        server.process.stdin.flush()
        self.assertEqual([self.receive(server) for _ in incoming], [
            {'status': 'success', 'value': 'alice-new'}, {'status': 'input', 'value': None},
            {'status': 'authentication', 'value': None}, {'status': 'refusal', 'value': 'cancelled'},
            {'status': 'success', 'value': 'bob-new'}], server.diagnostics())

        folder = ROOT/'examples/access'
        code, proof = ((folder/name).read_text() for name in ('Client.bend', 'ClientProof.bend'))
        receipt = server.prepared(0, code, 'alice-new', proof=universal_access_proof(proof))
        self.assertEqual(receipt['status'], 'prepared', server.diagnostics())
        handle = receipt['value']
        incoming = [prepared_frame(1, handle, 'alice-new', 'final'),
                    prepared_frame(1, handle, 'alice-new'),
                    prepared_frame(2, handle, 'final'),
                    prepared_frame(1, handle, 'final'), self.ordinary('final')]
        server.process.stdin.write(b''.join(incoming))
        server.process.stdin.close()  # EOF must drain queued work, including controls
        self.assertEqual([self.receive(server) for _ in incoming], [
            {'status': 'success', 'value': 'final'}, {'status': 'authentication', 'value': None},
            {'status': 'invalidated', 'value': None}, {'status': 'failure', 'value': None},
            {'status': 'refusal', 'value': 'cancelled'}], server.diagnostics())
        server.finish()

    def test_read_ahead_terminals_follow_real_transaction_and_complete_invalid_frame(self):
        for ending, status in [(b'', None), (b'\0'*7, 'input'),
                               ((4).to_bytes(8, 'big')+b'x', 'input'),
                               ((32769).to_bytes(8, 'big'), 'limit')]:
            with self.subTest(terminal=status, ending=ending):
                server = self.server()
                server.process.stdin.write(self.ordinary('alice-token', 'new') + frame(None) + ending)
                server.process.stdin.close()
                self.assertEqual(self.receive(server), {'status': 'success', 'value': 'new'}, server.diagnostics())
                self.assertEqual(self.receive(server), {'status': 'input', 'value': None})
                if status:
                    self.assertEqual(self.receive(server), {'status': status, 'value': None})
                server.finish()

    def test_closed_output_stops_later_dispatch_and_cleans_workers_without_input_eof(self):
        with tempfile.TemporaryDirectory(prefix='jaydb-scheduling-') as temporary:
            folder = Path(temporary)
            node = folder/'node'
            node.write_text('#!/bin/sh\nprintf "%s\\n" "$@" >> "$JAYDB_SCHEDULING_LOG"\n'
                            'exec "$JAYDB_SCHEDULING_NODE" "$@"\n')
            node.chmod(0o700)
            log = folder/'node-calls'
            env = dict(os.environ, TMPDIR=str(folder), PATH=str(folder)+os.pathsep+os.environ['PATH'],
                       JAYDB_SCHEDULING_LOG=str(log), JAYDB_SCHEDULING_NODE=shutil.which('node'))
            server = self.server(env)
            # Wait for actual initialization before closing the response pipe.
            self.assertEqual(server.call('bad', 'bad', 'invalid'), {'status': 'authentication', 'value': None})
            private, = folder.glob('jaydb2-*')
            server.process.stdout.close()
            server.process.stdin.write(self.ordinary('alice-token', 'new') +
                                       self.ordinary('new', 'must-not-run') + self.ordinary('bob-token', 'no'))
            server.process.stdin.flush()  # intentionally KEEP input open
            self.assertEqual(server.process.wait(timeout=180), 0, server.diagnostics())
            self.assertEqual(log.read_text().splitlines().count('execute'), 1,
                             'queued request entered admission after failed response delivery')
            self.assertFalse(private.exists(), 'owned prepared/request/native artifacts leaked')


if __name__ == '__main__':
    unittest.main(verbosity=2)
