"""Checked read admission and real native read execution; FIFO tests below."""
import json
import os
import socket
import subprocess
from pathlib import Path
import tempfile
import unittest

from tests.service.test_end_to_end import ROOT, Server
from tests.service.test_prepared import universal_access_proof
from tools.client import prepared_frame, unframe

CODE = (ROOT/'experiments/concurrency/Read.bend').read_text()
PROOF = (ROOT/'experiments/concurrency/ReadProof.bend').read_text()


class ReadBatchTests(unittest.TestCase):
    def test_single_reader_reuses_durable_root_and_preserves_authentication_and_barriers(self):
        with tempfile.TemporaryDirectory(prefix='jaydb-single-read-') as temporary:
            directory = Path(temporary)
            storage, timing = directory/'db', directory/'timing.ndjson'
            server = Server(ROOT/'examples/credential-exchange', threads=1,
                            options=['--storage', str(storage), '--storage-mode', 'create',
                                     '--timing-log', str(timing)])
            self.addCleanup(server.close)
            read = server.prepared(3, CODE, 'alice-token', proof=PROOF)
            self.assertEqual(read['status'], 'prepared', server.diagnostics())
            handle = read['value']
            image = storage/'snapshot'
            before, inode = image.read_bytes(), image.stat().st_ino
            for credential, arguments, expected in [
                ('alice-token', None, {'status': 'success', 'value': 'alice-token'}),
                ('bob-token', 37, {'status': 'success', 'value': 37}),
                ('invalid', None, {'status': 'authentication', 'value': None}),
                ('alice-token', True, {'status': 'failure', 'value': None}),
            ]:
                self.assertEqual(server.prepared(1, handle, credential, arguments),
                                 expected, server.diagnostics())
                self.assertEqual(image.read_bytes(), before)
                self.assertEqual(image.stat().st_ino, inode,
                                 'certified singleton read must not replace the durable root')
            records = [json.loads(line) for line in timing.read_text().splitlines()]
            self.assertEqual([r['read_batch'] for r in records], [False, True, True, True, True])
            # A read-shaped program without the additional read certificate still
            # follows ordinary durable publication, including replacing its image.
            ordinary_proof = PROOF.replace('def B.read_only(ctx, args):\n  (2n, read_only(ctx, args))', '')
            ordinary = server.prepared(0, CODE, 'alice-token', proof=ordinary_proof)
            self.assertEqual(ordinary['status'], 'prepared', server.diagnostics())
            self.assertEqual(server.prepared(1, ordinary['value'], 'alice-token'),
                             {'status': 'success', 'value': 'alice-token'})
            self.assertNotEqual(image.stat().st_ino, inode,
                                'uncertified reads retain the ordinary commit boundary')
            writecode = (ROOT/'examples/credentials/Client.bend').read_text()
            writeproof = universal_access_proof((ROOT/'examples/credentials/ClientProof.bend').read_text())
            write = server.prepared(0, writecode, 'alice-token', proof=writeproof)
            self.assertEqual(write['status'], 'prepared', server.diagnostics())
            messages = [
                prepared_frame(1, handle, 'alice-token', 11),
                prepared_frame(1, write['value'], 'alice-token', 'fresh-token'),
                prepared_frame(1, handle, 'alice-token'),
                prepared_frame(1, handle, 'fresh-token'),
                prepared_frame(2, handle, 'fresh-token'),
                prepared_frame(1, handle, 'fresh-token'),
            ]
            server.process.stdin.write(b''.join(messages))
            server.process.stdin.flush()
            for expected in [
                {'status': 'success', 'value': 11},
                {'status': 'success', 'value': 'fresh-token'},
                {'status': 'authentication', 'value': None},
                {'status': 'success', 'value': 'fresh-token'},
                {'status': 'invalidated', 'value': None},
                {'status': 'failure', 'value': None},
            ]:
                header = server.read(8)
                self.assertEqual(unframe(header+server.read(int.from_bytes(header, 'big'))),
                                 expected, server.diagnostics())
            self.assertIn(b'fresh-token', image.read_bytes())
            self.assertNotIn(b'alice-token', image.read_bytes())
            server.finish()
            reopened = Server(ROOT/'examples/credential-exchange', threads=1, seed=False,
                              options=['--storage', str(storage), '--storage-mode', 'open'])
            self.addCleanup(reopened.close)
            self.assertEqual(reopened.prepared(1, handle, 'fresh-token'),
                             {'status': 'failure', 'value': None}, 'restart must lose prepared handles')
            read = reopened.prepared(3, CODE, 'fresh-token', proof=PROOF)
            self.assertEqual(read['status'], 'prepared', reopened.diagnostics())
            inode = image.stat().st_ino
            self.assertEqual(reopened.prepared(1, read['value'], 'fresh-token'),
                             {'status': 'success', 'value': 'fresh-token'})
            self.assertEqual(image.stat().st_ino, inode)
            reopened.finish()

    def test_checked_read_preparation_and_native_failures(self):
        server = Server(ROOT/'examples/credential-exchange', threads=2, options=['--read-workers', '2'])
        self.addCleanup(server.close)
        receipt = server.prepared(3, CODE, 'alice-token', proof=PROOF)
        self.assertEqual(receipt['status'], 'prepared', server.diagnostics())
        handle = receipt['value']
        self.assertEqual(server.prepared(1, handle, 'alice-token'),
                         {'status': 'success', 'value': 'alice-token'}, server.diagnostics())
        self.assertEqual(server.prepared(1, handle, 'bob-token', 100000),
                         {'status': 'success', 'value': 100000}, server.diagnostics())
        for value in [-(2**63), 2**63-1]:
            self.assertEqual(server.prepared(1, handle, 'alice-token', value),
                             {'status': 'success', 'value': value})
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

    def test_real_overlapping_reads_fifo_credentials_control_and_delivery_failure(self):
        scratch = ROOT/'build/concurrency'
        scratch.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='read-gate-', dir=scratch) as temporary:
            directory = Path(temporary)
            library = directory/'gate.so'
            subprocess.run(['cc', '-shared', '-fPIC', str(ROOT/'tests/service/read_gate.c'),
                            '-o', str(library), '-ldl'], check=True)
            # Unix paths are capped at 108 bytes; use a local relative path.
            gatepath = directory/'g'
            # TMPDIR may have a long worktree prefix. A local relative path is
            # resolved against the common server/test cwd and stays local.
            gatepath = gatepath.relative_to(ROOT)
            gate = socket.socket(socket.AF_UNIX)
            self.addCleanup(gate.close)
            gate.bind(str(gatepath))
            gate.listen(16)
            gate.settimeout(30)
            targets = directory/'targets'
            targets.write_text('')
            env = dict(os.environ, LD_PRELOAD=str(library), JAYDB_TEST_READ_GATE=str(gatepath),
                       JAYDB_TEST_READ_TARGETS=str(targets))
            server = Server(ROOT/'examples/credential-exchange', env=env, threads=2,
                            options=['--read-workers', '2', '--storage', str(directory/'db'), '--storage-mode', 'create'])
            self.addCleanup(server.close)
            read = server.prepared(3, CODE, 'alice-token', proof=PROOF)
            self.assertEqual(read['status'], 'prepared', server.diagnostics())
            writecode = (ROOT/'examples/credentials/Client.bend').read_text()
            writeproof = universal_access_proof((ROOT/'examples/credentials/ClientProof.bend').read_text())
            write = server.prepared(0, writecode, 'alice-token', proof=writeproof)
            self.assertEqual(write['status'], 'prepared', server.diagnostics())
            private = next(Path(tempfile.gettempdir()).glob(f'jaydb2-{server.process.pid}-*'))
            programs = {code: next(p.glob('*.program')) for p in private.glob('request-*')
                        if (code := (p/'Client.bend').read_text()) in (CODE, writecode)}
            targets.write_text(''.join(str(programs[c])+'\n' for c in (CODE, writecode)))
            def held(code):
                connection, _ = gate.accept()
                self.addCleanup(connection.close)
                connection.settimeout(30)
                info = connection.recv(4200).decode().strip().split(' ', 1)
                self.assertEqual(Path(info[1]), programs[code])
                self.assertTrue(Path('/proc', info[0]).exists(), 'real native process must be alive')
                return connection
            def release(connection, command=b'r'):
                connection.sendall(command)
                connection.close()
            def response():
                header = server.read(8)
                return unframe(header + server.read(int.from_bytes(header, 'big')))
            def send(messages):
                server.process.stdin.write(b''.join(messages))
                server.process.stdin.flush()
            rh, wh = read['value'], write['value']
            send([prepared_frame(1, wh, 'alice-token', 'phase1'),
                  prepared_frame(1, rh, 'phase1', 11),
                  prepared_frame(1, rh, 'phase1', 22),
                  prepared_frame(1, wh, 'phase1', 'phase2'),
                  prepared_frame(1, rh, 'phase1'),
                  prepared_frame(1, rh, 'phase2'),
                  prepared_frame(1, rh, 'phase2', True),
                  prepared_frame(1, rh, 'phase2'),
                  prepared_frame(2, rh, 'phase2'),
                  prepared_frame(1, rh, 'phase2')])
            firstwrite = held(writecode)  # read-ahead fills while exclusive work is held
            release(firstwrite)
            self.assertEqual(response(), {'status':'success', 'value':'phase1'})
            first, second = held(CODE), held(CODE)  # neither released: real overlap
            release(second)
            release(first)
            self.assertEqual(response(), {'status':'success', 'value':11})
            self.assertEqual(response(), {'status':'success', 'value':22})
            secondwrite = held(writecode)
            release(secondwrite)
            self.assertEqual(response(), {'status':'success', 'value':'phase2'})
            later = held(CODE)
            release(later)
            self.assertEqual(response(), {'status':'authentication', 'value':None})
            self.assertEqual(response(), {'status':'success', 'value':'phase2'})
            first, second = held(CODE), held(CODE)
            release(second)
            release(first)
            self.assertEqual(response(), {'status':'failure', 'value':None})
            self.assertEqual(response(), {'status':'success', 'value':'phase2'})
            self.assertEqual(response(), {'status':'invalidated', 'value':None})
            self.assertEqual(response(), {'status':'failure', 'value':None})
            # Reprepare, then hold an exclusive write so both reads are queued.
            read = server.prepared(3, CODE, 'phase2', proof=PROOF)
            self.assertEqual(read['status'], 'prepared', server.diagnostics())
            newest = next(p for p in private.glob('request-*') if (p/'Client.bend').read_text() == CODE)
            programs[CODE] = next(newest.glob('*.program'))
            targets.write_text(''.join(str(programs[c])+'\n' for c in (CODE, writecode)))
            send([prepared_frame(1, wh, 'phase2', 'phase2'),
                  prepared_frame(1, read['value'], 'phase2'),
                  prepared_frame(1, read['value'], 'phase2'),
                  prepared_frame(1, wh, 'phase2', 'must-not-run')])
            release(held(writecode))
            self.assertEqual(response(), {'status':'success', 'value':'phase2'})
            first, second = held(CODE), held(CODE)
            server.process.stdout.close()  # actual host pipe failure with another read active
            release(first)
            self.assertIsNone(server.process.poll())
            release(second)
            self.assertEqual(server.process.wait(timeout=30), 0, server.diagnostics())
            gate.settimeout(0.1)
            with self.assertRaises(socket.timeout): gate.accept()  # queued write never launched
            reopened = Server(ROOT/'examples/credential-exchange', env=env, threads=2, seed=False,
                              options=['--read-workers', '2', '--storage', str(directory/'db'),
                                       '--storage-mode', 'open'])
            self.addCleanup(reopened.close)
            # Reads do not rewrite the durable root; the last exclusive credential
            # change survives, and the write behind failed delivery never ran.
            self.assertEqual(reopened.prepared(1, read['value'], 'phase1'),
                             {'status':'authentication', 'value':None})
            self.assertEqual(reopened.prepared(1, read['value'], 'phase2'),
                             {'status':'failure', 'value':None})  # handles are ephemeral
            fresh = reopened.prepared(3, CODE, 'phase2', proof=PROOF)
            self.assertEqual(fresh['status'], 'prepared', reopened.diagnostics())
            self.assertEqual(reopened.prepared(1, fresh['value'], 'phase2'),
                             {'status':'success', 'value':'phase2'}, reopened.diagnostics())
            reopened.finish()


if __name__ == '__main__':
    unittest.main(verbosity=2)
