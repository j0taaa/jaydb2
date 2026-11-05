"""Real CLI -> official Bend checking/C -> child workers -> publication."""
import os
from pathlib import Path
import select
import signal
import subprocess
import tempfile
import time
import unittest

from tools.client import frame, prepared_frame, unframe

ROOT = Path(__file__).resolve().parents[2]


class Server:
    """Development harness for the actual controller, with a reference override."""
    def __init__(self, folder, env=None, command_prefix=(), threads=None,
                 binary=None, arguments=(), seed=True):
        env = dict(os.environ if env is None else env)
        env.setdefault('TMPDIR', str(ROOT/'target/test-tmp'))
        self.temporary_root = Path(env['TMPDIR'])
        self.temporary_root.mkdir(parents=True, exist_ok=True)
        self.errors = tempfile.TemporaryFile()
        command = [str(binary or os.environ.get('JAYDB2_TEST_HOST', ROOT/'jaydb2')),
                   '--configuration', str(folder/'Configuration.bend')]
        if seed:
            command.extend(['--seed', str(folder/'Seed.bend')])
        command.extend(arguments)
        if threads is not None:
            command.extend(['--threads', str(threads)])
        self.process = subprocess.Popen([*command_prefix, *command], cwd=ROOT,
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=self.errors,
            start_new_session=True, env=env)

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
        return self.exchange(frame({'code': code, 'proof': proof,
                                    'credential': credential, 'arguments': arguments}))

    def prepared(self, operation, code, credential, arguments=None, proof=''):
        return self.exchange(prepared_frame(operation, code, credential, arguments, proof))

    def exchange(self, message):
        self.process.stdin.write(message)
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
    def test_native_runtime_options_are_owned_by_host(self):
        from tests.service.test_prepared import universal_access_proof
        folder = ROOT/'examples/access'
        code, proof = ((folder/name).read_text() for name in ('Client.bend', 'ClientProof.bend'))
        server = Server(folder, env=dict(os.environ, BENDRTS='--gpu-build --help'))
        self.addCleanup(server.close)
        self.assertEqual(server.call(code, proof, 'alice-token', 'one'),
                         {'status': 'success', 'value': 'one'}, server.diagnostics())
        receipt = server.prepared(0, code, 'one', proof=universal_access_proof(proof))
        self.assertEqual(receipt['status'], 'prepared', server.diagnostics())
        self.assertEqual(server.prepared(1, receipt['value'], 'one', 'two'),
                         {'status': 'success', 'value': 'two'}, server.diagnostics())
        server.finish()

    def server(self, folder):
        server = Server(folder)
        self.addCleanup(server.close)
        return server

    def test_transaction_rollback_publication_and_authenticated_identity(self):
        # A final duplicate rolls back; exchanging credentials publishes once
        # and changes authentication, while each call keeps its initial actor.
        folder = ROOT/'examples/credential-exchange'
        temporary = tempfile.TemporaryDirectory(prefix='jaydb-import-test-')
        self.addCleanup(temporary.cleanup)
        instance = Path(temporary.name)
        # This library has no other import path. Staging must collect TAB just
        # as preflight does, only the actual checker/compiler can resolve it.
        (instance/'Sizes.bend').write_text('import Base\ndef message() -> Nat:\n  32768n\n')
        configuration = (folder/'Configuration.bend').read_text()
        self.assertEqual(configuration.count('S.Limits{32768n, 65536n, 32768n}'), 1)
        (instance/'Configuration.bend').write_text('import\t./Sizes.bend\tas\tSizes\n' +
            configuration.replace('S.Limits{32768n, 65536n, 32768n}',
                                  'S.Limits{Sizes.message(), 65536n, 32768n}'))
        (instance/'Seed.bend').write_bytes((folder/'Seed.bend').read_bytes())
        server = self.server(instance)
        code = (folder/'Client.bend').read_text()
        proof = (folder/'ClientProof.bend').read_text()
        self.assertEqual(server.call(code, proof, 'alice-token', ['same', 'same']),
                         {'status': 'data', 'value': None}, server.diagnostics())
        self.assertEqual(server.call(code, proof, 'alice-token'),
                         {'status': 'success', 'value': 'bob-token'}, server.diagnostics())
        self.assertEqual(server.call((folder/'Who.bend').read_text(),
                                    (folder/'WhoProof.bend').read_text(), 'alice-token'),
                         {'status': 'success', 'value': 'bob'}, server.diagnostics())
        self.assertEqual(server.call(code, proof, 'invalid-token'),
                         {'status': 'authentication', 'value': None}, server.diagnostics())
        server.finish()

    def test_initialization_rejects_another_environment_identity(self):
        with tempfile.TemporaryDirectory(prefix='jaydb-identity-test-') as temporary:
            folder = Path(temporary)
            original = ROOT/'examples/credentials'
            (folder/'Seed.bend').write_bytes((original/'Seed.bend').read_bytes())
            source = (original/'Configuration.bend').read_text()
            self.assertEqual(source.count('E.identity()'), 1)
            (folder/'Configuration.bend').write_text(source.replace('E.identity()', '"other-environment"'))
            result = subprocess.run([os.environ.get('JAYDB2_TEST_HOST', str(ROOT/'jaydb2')), '--configuration', str(folder/'Configuration.bend'),
                                     '--seed', str(folder/'Seed.bend')], input=b'', capture_output=True,
                                    cwd=ROOT, timeout=180)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(result.stdout, b'')
            self.assertIn(b'invalid configuration or initial state', result.stderr)

    def test_access_laws_cover_refusal_and_failed_child(self):
        # Real, nontrivial administrator law: every read/write addresses only
        # the authenticated user's credential. Even a later refusal must obey.
        folder = ROOT/'examples/access'
        code, proof = ((folder/name).read_text() for name in ('Client.bend', 'ClientProof.bend'))
        server = self.server(folder)
        self.assertEqual(server.call(code, proof, 'alice-token', 'alice-new'),
                         {'status': 'success', 'value': 'alice-new'}, server.diagnostics())
        self.assertEqual(server.call(code, proof, 'alice-token'),
                         {'status': 'authentication', 'value': None}, server.diagnostics())
        self.assertEqual(server.call(code, proof, 'alice-new'),
                         {'status': 'refusal', 'value': 'cancelled'}, server.diagnostics())

        read = 'D.ReadCell{D.Users{}, id, "credential"}'
        write = 'D.DefineColumn{D.Users{}, id, "credential",'
        self.assertEqual(code.count(read), 1)
        self.assertEqual(code.count(write), 1)
        forbidden_read = code.replace(read, 'D.ReadCell{D.Users{}, "bob", "credential"}')
        forbidden_write = code.replace(write, 'D.DefineColumn{D.Users{}, "bob", "credential",')
        forged_actor = code.replace('arguments(id, args)', 'arguments("bob", args)')
        self.assertNotEqual(forged_actor, code)
        for name, changed, arguments in [('read', forbidden_read, 'blocked'),
                                        ('write', forbidden_write, 'blocked'),
                                        ('read-then-refuse', forbidden_read, None),
                                        ('forged-actor', forged_actor, 'blocked')]:
            with self.subTest(case=name):
                self.assertEqual(server.call(changed, proof, 'alice-new', arguments),
                                 {'status': 'certificate', 'value': None}, server.diagnostics())
        # No incomplete proof or missing dependency accounts for those refusals.
        self.assertIn('PRIMARY_CHECK', server.diagnostics())
        self.assertNotIn('Metavari', server.diagnostics())

        # The supplied proof is insensitive to the terminal value. The official
        # checker accepts this code, but the actual native child cannot represent
        # the consumed Nat product 2^48. No fake process or injected result.
        terminal = 'S.Finish{value}'
        self.assertEqual(code.count(terminal), 1)
        failing = code.replace(terminal,
            'S.Finish{D.VInt{0, U32.from_nat(Nat.mul(16777216n, 16777216n))}}')
        before = len(server.diagnostics())
        self.assertEqual(server.call(failing, proof, 'alice-new', 'never-published'),
                         {'status': 'failure', 'value': None}, server.diagnostics())
        failure = server.diagnostics()[before:]
        self.assertIn('NATIVE', failure)
        self.assertIn('a Nat past the largest immediate', failure)
        # Both legitimate refusal and child failure left the old credential
        # published; a separate actor still updates only its own record.
        self.assertEqual(server.call(code, proof, 'alice-new', 'alice-new'),
                         {'status': 'success', 'value': 'alice-new'}, server.diagnostics())
        self.assertEqual(server.call(code, proof, 'bob-token', 'bob-new'),
                         {'status': 'success', 'value': 'bob-new'}, server.diagnostics())
        self.assertEqual(server.call(code, proof, 'alice-new', 'alice-new'),
                         {'status': 'success', 'value': 'alice-new'}, server.diagnostics())
        server.finish()


if __name__ == '__main__':
    unittest.main(verbosity=2)
