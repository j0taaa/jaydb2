"""Durable receipt with lost acknowledgement, restart, and observable write counts.

Run make test-idempotency-recovery under the shared heavy lock. Only the
opt-in storage-fault binary has the barrier; production builds have no hook.
"""
import hashlib
import os
import resource
from pathlib import Path
import shutil
import signal
import socket
import subprocess
import tempfile
import unittest

from applications.vouchers.check import prepare
from tests.service.test_end_to_end import ROOT, Server
from tests.service.test_persistence import state_bytes
from tools.client import decode, encode, prepared_frame

BINARY = Path(os.environ.get('JAYDB_IDEMPOTENCY_BINARY',
    ROOT/'.build/idempotency/fault/release/jaydb2'))


class ReceiptRecoveryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # The normal ./jaydb2 launcher does this before exec. This test uses a
        # direct fault-build binary so it must establish the same OS limit.
        previous = resource.getrlimit(resource.RLIMIT_STACK)
        resource.setrlimit(resource.RLIMIT_STACK, (previous[1], previous[1]))
        cls.addClassCleanup(resource.setrlimit, resource.RLIMIT_STACK, previous)

    def compile_trace(self, folder):
        folder.mkdir()
        prepare(folder)
        for parent in ('contract', 'src'):
            for source in (ROOT/parent).glob('*.bend'):
                (folder/source.name).write_text(source.read_text().replace('../contract/', './'))
        (folder/'Environment.bend').write_text('import Base\ndef identity() -> String: "receipt-trace-test"\n')
        shutil.copyfile(ROOT/'native/effects.bend', folder/'Native.bend')
        shutil.copyfile(ROOT/'native/effects.c', folder/'effects.c')
        shutil.copyfile(ROOT/'tests/service/ReceiptTrace.bend', folder/'Trace.bend')
        source, binary = folder/'trace.c', folder/'trace'
        subprocess.run(['node', '--stack_size=65536', str(ROOT/'tests/native/emit_fixture.mjs'),
            str(ROOT/'.tools/bend-source-2.0.39/bend2'), str(folder/'Trace.bend'), str(source)],
            check=True, timeout=120)
        emitted = hashlib.sha256(source.read_bytes()).digest()
        subprocess.run(['/usr/bin/clang-19', '-std=gnu11', '-O2', '-w', '--no-default-config',
            str(source), '-o', str(binary), '-lm', '-pthread'], check=True, timeout=120)
        self.assertEqual(hashlib.sha256(source.read_bytes()).digest(), emitted)
        return binary

    def audit(self, binary, state, args, business, receipt, status='success', value='v:lost'):
        request = encode(dict(credential='alice-token', code='', proof='', arguments=args))
        packet = len(state).to_bytes(8, 'big') + state + request
        result = subprocess.run([str(binary), '+RTS', '--threads', '1', '--gpu', 'off', '-RTS'],
            input=packet, capture_output=True, check=True, timeout=60,
            env=dict(os.environ, BENDRTS=''))
        self.assertEqual(decode(result.stdout), dict(business_writes=business,
            receipt_writes=receipt, response=dict(status=status, value=value)))

    def test_lost_response_retries_original_receipt_without_reexecuting_business_writes(self):
        self.assertTrue(BINARY.is_file(), 'Build the opt-in fault binary with make test-idempotency-recovery')
        build = ROOT/'.build/idempotency'; build.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='receipt-recovery-', dir=build) as temporary:
            folder = Path(temporary); app = folder/'app'; app.mkdir(); prepare(app)
            storage = folder/'db'
            code, proof = ((app/name).read_text() for name in ('Client.bend', 'ClientProof.bend'))
            # Create unarmed. Opening never persists the seed, so the armed
            # barrier is reached only by the selected business operation.
            initial = Server(app, binary=BINARY, threads=1,
                arguments=['--storage', str(storage), '--storage-mode', 'create'])
            self.addCleanup(initial.close)
            self.assertEqual(initial.call(code, proof, 'invalid')['status'], 'authentication')
            initial.finish()
            before = state_bytes(storage)
            trace = self.compile_trace(folder/'trace')
            args = ['issue', 'lost', 'durable', False]
            # Fresh positive control proves the oracle sees real writes.
            self.audit(trace, before, args, business=1, receipt=1)
            # Short, private Unix path, independent of an inherited long TMPDIR.
            with tempfile.TemporaryDirectory(prefix='jaydb-receipt-barrier-', dir='/tmp') as gate:
                path = str(Path(gate)/'socket')
                with socket.socket(socket.AF_UNIX) as listener:
                    listener.bind(path); listener.listen(1); listener.settimeout(180)
                    env = dict(os.environ, JAYDB_STORAGE_FAULT='after_data_sync',
                               JAYDB_STORAGE_BARRIER=path)
                    pending = Server(app, binary=BINARY, threads=1, env=env, seed=False,
                        arguments=['--storage', str(storage), '--storage-mode', 'open'])
                    self.addCleanup(pending.close)
                    old = 'def B.certificate(s, valid, identity, n):\n  certify(I.context(), I.arguments(), B.code(), s, valid, identity, n)'
                    new = 'def B.certificate(ctx, args, s, valid, identity, n):\n  certify(ctx, args, B.code(), s, valid, identity, n)'
                    self.assertIn(old, proof)
                    universal = proof.replace(old, new)
                    prepared = pending.prepared(0, code, 'alice-token', proof=universal)
                    self.assertEqual(prepared['status'], 'prepared', pending.diagnostics())
                    request = prepared_frame(1, prepared['value'], 'alice-token', args)
                    later = prepared_frame(1, prepared['value'], 'alice-token', ['issue', 'later', 'queued', False])
                    pending.process.stdin.write(request+later); pending.process.stdin.flush()
                    stream, _ = listener.accept()
                    with stream:
                        stream.settimeout(30)
                        expected = b'after_data_sync'; received = bytearray()
                        while len(received) < len(expected):
                            part = stream.recv(len(expected)-len(received))
                            self.assertTrue(part); received.extend(part)
                        self.assertEqual(received, expected)
                        committed = state_bytes(storage)
                        self.assertNotEqual(committed, before)
                        # All request workers were cleaned up before durability.
                        children = Path(f'/proc/{pending.process.pid}/task/{pending.process.pid}/children')
                        self.assertEqual(children.read_text().strip(), '')
                        os.kill(pending.process.pid, signal.SIGKILL)
                        pending.process.wait(timeout=10)
                    self.assertEqual(pending.process.stdout.read(), b'', 'no acknowledgement or later response may escape')
            image = (storage/'snapshot').read_bytes()
            # Hold the old inode live so an accidental rewrite cannot hide
            # behind inode-number reuse. Recovery and receipt hits reuse it.
            durable_file = (storage/'snapshot').open('rb')
            self.addCleanup(durable_file.close)
            durable_inode = os.fstat(durable_file.fileno()).st_ino
            tables = {table['name']: table['rows'] for table in decode(committed)['tables']}
            self.assertEqual({r['id'] for r in tables['alice']}, {'permission','r:lost','v:lost'})
            self.assertEqual({r['id'] for r in tables['bob']}, {'permission'})
            # No counter/schema extension is needed: inspect the actual Core
            # events on the recovered bytes to distinguish a receipt hit from
            # rewriting the same deterministic business row a second time.
            self.audit(trace, committed, args, business=0, receipt=0)
            conflict = ['issue', 'lost', 'changed', False]
            self.audit(trace, committed, conflict, business=0, receipt=0,
                       status='refusal', value='request conflict')
            (app/'Seed.bend').unlink()
            retry = Server(app, binary=BINARY, threads=1, seed=False,
                arguments=['--storage', str(storage), '--storage-mode', 'open'])
            self.addCleanup(retry.close)
            self.assertEqual(retry.call(code, proof, 'alice-token', args),
                             dict(status='success', value='v:lost'), retry.diagnostics())
            self.assertEqual((storage/'snapshot').read_bytes(), image)
            self.assertEqual(retry.call(code, proof, 'alice-token', conflict),
                             dict(status='refusal', value='request conflict'))
            self.assertEqual(retry.call(code, proof, 'alice-token', ['inspect','lost']),
                             dict(status='success', value='durable'))
            self.assertEqual(retry.call(code, proof, 'alice-token', ['inspect','later']),
                             dict(status='success', value=None))
            self.assertEqual(state_bytes(storage), committed)
            self.assertEqual((storage/'snapshot').stat().st_ino, durable_inode,
                             'receipt hits and reads must reuse the durable image')
            retry.finish()


if __name__ == '__main__':
    unittest.main(verbosity=2)
