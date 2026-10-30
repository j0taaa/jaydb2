"""Real CLI -> official Bend checking/C -> child workers -> publication."""
import os
from pathlib import Path
import select
import signal
import subprocess
import tempfile
import time
import unittest

from tools.client import frame, unframe

ROOT = Path(__file__).resolve().parents[2]


class Server:
    """Development harness only; the production server is the Rust executable."""
    def __init__(self, folder):
        self.errors = tempfile.TemporaryFile()
        self.process = subprocess.Popen([
            str(ROOT/'jaydb2'), '--configuration', str(folder/'Configuration.bend'),
            '--seed', str(folder/'Seed.bend')], cwd=ROOT,
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=self.errors,
            start_new_session=True)

    def diagnostics(self):
        return os.pread(self.errors.fileno(), os.fstat(self.errors.fileno()).st_size, 0).decode('utf-8', 'replace')

    def read(self, size):
        result = bytearray()
        deadline = time.monotonic() + 180  # CI guard, never a server guarantee.
        while len(result) < size:
            remaining = deadline - time.monotonic()
            if remaining <= 0 or not select.select([self.process.stdout], [], [], max(remaining, 0))[0]:
                raise AssertionError('CLI response timed out\n' + self.diagnostics())
            chunk = os.read(self.process.stdout.fileno(), size-len(result))
            if not chunk:
                raise AssertionError('CLI ended before a complete response\n' + self.diagnostics())
            result.extend(chunk)
        return bytes(result)

    def call(self, code, proof, credential, arguments=None):
        self.process.stdin.write(frame({'codigo': code, 'prova': proof,
                                        'credencial': credential, 'argumentos': arguments}))
        self.process.stdin.flush()
        header = self.read(8)
        return unframe(header + self.read(int.from_bytes(header, 'big')))

    def finish(self):
        self.process.stdin.close()
        code = self.process.wait(timeout=30)
        if code:
            raise AssertionError(f'CLI exited {code}\n' + self.diagnostics())
        if self.process.stdout.read():
            raise AssertionError('Unexpected bytes after the response frames')

    def close(self):
        if self.process.poll() is None:
            try:
                os.killpg(self.process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            self.process.wait(timeout=10)
        for stream in (self.process.stdin, self.process.stdout):
            stream.close()
        self.errors.close()


class EndToEndTests(unittest.TestCase):
    def server(self, folder):
        server = Server(folder)
        self.addCleanup(server.close)
        return server

    def test_transaction_rollback_publication_and_authenticated_identity(self):
        # A final duplicate rolls back; exchanging credentials publishes once
        # and changes authentication, while each call keeps its initial actor.
        folder = ROOT/'examples/troca-credenciais'
        server = self.server(folder)
        code = (folder/'Client.bend').read_text()
        proof = (folder/'ClientProof.bend').read_text()
        self.assertEqual(server.call(code, proof, 'alice-token', ['same', 'same']),
                         {'status': 'dados', 'valor': None}, server.diagnostics())
        self.assertEqual(server.call(code, proof, 'alice-token'),
                         {'status': 'sucesso', 'valor': 'bob-token'}, server.diagnostics())
        self.assertEqual(server.call((folder/'Quem.bend').read_text(),
                                    (folder/'QuemProof.bend').read_text(), 'alice-token'),
                         {'status': 'sucesso', 'valor': 'bob'}, server.diagnostics())
        self.assertEqual(server.call(code, proof, 'invalid-token'),
                         {'status': 'autenticacao', 'valor': None}, server.diagnostics())
        server.finish()

    def test_initialization_rejects_another_environment_identity(self):
        with tempfile.TemporaryDirectory(prefix='jaydb-identity-test-') as temporary:
            folder = Path(temporary)
            original = ROOT/'examples/credenciais'
            (folder/'Seed.bend').write_bytes((original/'Seed.bend').read_bytes())
            source = (original/'Configuration.bend').read_text()
            self.assertEqual(source.count('E.identidade()'), 1)
            (folder/'Configuration.bend').write_text(source.replace('E.identidade()', '"other-environment"'))
            result = subprocess.run([str(ROOT/'jaydb2'), '--configuration', str(folder/'Configuration.bend'),
                                     '--seed', str(folder/'Seed.bend')], input=b'', capture_output=True,
                                    cwd=ROOT, timeout=180)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, b'')
            self.assertIn(b'invalid configuration or initial state', result.stderr)

    def test_access_laws_cover_refusal_and_failed_child(self):
        # Real, nontrivial administrator law: every read/write addresses only
        # the authenticated user's credential. Even a later refusal must obey.
        folder = ROOT/'examples/acessos'
        code, proof = ((folder/name).read_text() for name in ('Client.bend', 'ClientProof.bend'))
        server = self.server(folder)
        self.assertEqual(server.call(code, proof, 'alice-token', 'alice-new'),
                         {'status': 'sucesso', 'valor': 'alice-new'}, server.diagnostics())
        self.assertEqual(server.call(code, proof, 'alice-token'),
                         {'status': 'autenticacao', 'valor': None}, server.diagnostics())
        self.assertEqual(server.call(code, proof, 'alice-new'),
                         {'status': 'recusa', 'valor': 'cancelado'}, server.diagnostics())

        read = 'D.LerCelula{D.Usuarios{}, id, "credencial"}'
        write = 'D.DefinirColuna{D.Usuarios{}, id, "credencial",'
        self.assertEqual(code.count(read), 1)
        self.assertEqual(code.count(write), 1)
        forbidden_read = code.replace(read, 'D.LerCelula{D.Usuarios{}, "bob", "credencial"}')
        forbidden_write = code.replace(write, 'D.DefinirColuna{D.Usuarios{}, "bob", "credencial",')
        forged_actor = code.replace('argumentos(id, args)', 'argumentos("bob", args)')
        self.assertNotEqual(forged_actor, code)
        for name, changed, arguments in [('read', forbidden_read, 'blocked'),
                                        ('write', forbidden_write, 'blocked'),
                                        ('read-then-refuse', forbidden_read, None),
                                        ('forged-actor', forged_actor, 'blocked')]:
            with self.subTest(case=name):
                self.assertEqual(server.call(changed, proof, 'alice-new', arguments),
                                 {'status': 'certificado', 'valor': None}, server.diagnostics())
        # No incomplete proof or missing dependency accounts for those refusals.
        self.assertIn('PRIMARY_CHECK', server.diagnostics())
        self.assertNotIn('Metavari', server.diagnostics())

        # The supplied proof is insensitive to the terminal value. The official
        # checker accepts this code, but the actual native child cannot represent
        # the consumed Nat product 2^48. No fake process or injected result.
        terminal = 'S.Terminar{valor}'
        self.assertEqual(code.count(terminal), 1)
        failing = code.replace(terminal,
            'S.Terminar{D.VInt{0, U32.from_nat(Nat.mul(16777216n, 16777216n))}}')
        before = len(server.diagnostics())
        self.assertEqual(server.call(failing, proof, 'alice-new', 'never-published'),
                         {'status': 'falha', 'valor': None}, server.diagnostics())
        failure = server.diagnostics()[before:]
        self.assertIn('NATIVE', failure)
        self.assertIn('a Nat past the largest immediate', failure)
        # Both legitimate refusal and child failure left the old credential
        # published; a separate actor still updates only its own record.
        self.assertEqual(server.call(code, proof, 'alice-new', 'alice-new'),
                         {'status': 'sucesso', 'valor': 'alice-new'}, server.diagnostics())
        self.assertEqual(server.call(code, proof, 'bob-token', 'bob-new'),
                         {'status': 'sucesso', 'valor': 'bob-new'}, server.diagnostics())
        self.assertEqual(server.call(code, proof, 'alice-new', 'alice-new'),
                         {'status': 'sucesso', 'valor': 'alice-new'}, server.diagnostics())
        server.finish()


if __name__ == '__main__':
    unittest.main(verbosity=2)
