"""Compare the removed two-process gate with the actual native authenticator.

Run under the experiments heavy lock. Optionally set JAYDB_PREPROCESS_TRACE to
an output filename to assert/count the real host's execve calls with strace.
The legacy decoder is compiled only by this test, outside service artifacts.
"""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from tests.service.test_end_to_end import ROOT, Server
from tools.client import encode, frame, prepared_frame, unframe


def packet(state, body):
    return len(state).to_bytes(8, 'big') + state + body


class PreprocessingTests(unittest.TestCase):
    def test_native_differential_and_host_error_precedence(self):
        with tempfile.TemporaryDirectory(prefix='jaydb-preprocessing-') as temporary:
            folder = Path(temporary)
            trace = os.environ.get('JAYDB_PREPROCESS_TRACE')
            prefix = ['strace', '-f', '-e', 'trace=execve', '-o', str(Path(trace).resolve())] if trace else []
            server = Server(ROOT/'examples/access', env=dict(os.environ, TMPDIR=str(folder)),
                            command_prefix=prefix, threads=1)
            self.addCleanup(server.close)
            # Completes initialization before inspecting the local artifacts.
            self.assertEqual(server.call('bad code', 'bad proof', 'invalid'),
                             {'status': 'authentication', 'value': None}, server.diagnostics())
            private, = folder.glob('jaydb2-*')
            self.assertFalse((private/'decode').exists())
            self.assertFalse(list(private.rglob('Seed.bend')))
            authenticator, = (private/'authenticate').glob('*.program')

            lock = json.loads((ROOT/'tools/admission/toolchain.lock.json').read_text())
            # Keep the old decode-only entry available for this differential
            # control; production initialize builds no such artifact.
            script = """import { execute } from './tools/service/stage.mjs';
              const [work, out, source, kernel] = process.argv.slice(1);
              console.log(JSON.stringify(execute(work, out, null, source, kernel, 'decode')));"""
            compiled = subprocess.run(['node', '--stack_size=65536', '--input-type=module', '-e', script,
                str(private), str(folder/'reference-decode'),
                str(ROOT/'.tools'/('bend-source-'+lock['version'])),
                str(ROOT/'.tools'/('bendtt-'+lock['kernelSha256']))],
                cwd=ROOT, capture_output=True, text=True, timeout=180)
            self.assertEqual(compiled.returncode, 0, compiled.stdout+compiled.stderr)
            decoder = Path(json.loads(compiled.stdout)['program'])
            state = encode({'tables': [], 'users': [
                {'credential': 'alice-token', 'id': 'alice', 'kind': 'user'},
                {'credential': 'bob-token', 'id': 'bob', 'kind': 'user'}]})

            def native(program, incoming):
                result = subprocess.run([str(program), '+RTS', '--threads', '1', '--gpu', 'off', '-RTS'],
                    input=incoming, capture_output=True, timeout=30)
                self.assertEqual(result.returncode, 0, result.stderr.decode('utf-8', 'replace'))
                return result.stdout

            def compare(incoming, status=None):
                decoded = native(decoder, incoming)
                old = native(authenticator, incoming) if decoded == b'\1' else decoded
                new = native(authenticator, incoming)
                self.assertEqual(new, old, 'single pass changed exact legacy output')
                if status:
                    self.assertEqual(new[0], 0)
                    self.assertEqual(unframe(new[1:]), {'status': status, 'value': None})
                return new

            def request(**updates):
                fields = dict(arguments=None, code='source-λ\r\n', credential='alice-token', proof='proof-雪')
                fields.update(updates)
                return encode(fields)

            def auth_fields(result):
                self.assertEqual(result[0], 1)
                fields, rest = [], result[1:]
                for _ in range(4):  # exact id, code, proof, instance
                    self.assertGreaterEqual(len(rest), 8)
                    size = int.from_bytes(rest[:8], 'big')
                    self.assertLessEqual(size, len(rest)-8)
                    fields.append(rest[8:8+size])
                    rest = rest[8+size:]
                fields.append(rest)  # Bindings.bend links remainder
                return fields

            # Exact code/proof strings, actual contexts and all public values
            # flow unchanged into the admission metadata, not just a status.
            positive = []
            for credential in ('alice-token', 'bob-token'):
                for arguments in (None, '', [-2**63, 2**63-1, True, False, {'text': 'λ雪\0'}]):
                    with self.subTest(credential=credential, arguments=arguments):
                        result = compare(packet(state, request(credential=credential, arguments=arguments)))
                        self.assertEqual(result[0], 1)
                        principal, code, proof, instance, links = auth_fields(result)
                        self.assertEqual(principal, credential.removesuffix('-token').encode())
                        self.assertEqual(code, 'source-λ\r\n'.encode())
                        self.assertEqual(proof, 'proof-雪'.encode())
                        self.assertIn(b'D.Context{"'+principal+b'","user"}', instance)
                        self.assertIn(b'law certificate:', links)
                        positive.append(result)
            self.assertEqual(len(set(positive)), 6, 'context/argument metadata was reused')
            # The principal is length-delimited UTF-8, even when its bytes
            # resemble source syntax. Metadata still binds the actual context.
            for identity in ('', 'λ雪\\"\n'):
                special_state = encode({'tables': [], 'users': [
                    {'credential': 'alice-token', 'id': identity, 'kind': 'user'}]})
                principal, code, proof, instance, links = auth_fields(compare(packet(special_state, request())))
                self.assertEqual(principal, identity.encode())
                self.assertEqual(code, 'source-λ\r\n'.encode())
                self.assertEqual(proof, 'proof-雪'.encode())
                self.assertIn(b'def context()', instance)
            compare(packet(state, request(credential='invalid', code='bad', proof='bad')), 'authentication')
            malformed = [b'', b'\7', b'\0', request()+b'\0',
                encode({'credential': 'invalid'}), request(credential=1),
                request(code=None, credential='invalid'), request(proof=[], credential='invalid'),
                b'\4'+(1).to_bytes(8, 'big')+b'\xff',
                b'\5'+(2**64-1).to_bytes(8, 'big'),
                b'\6'+(2).to_bytes(8, 'big')+encode('z')+b'\0'+encode('a')+b'\0']
            for body in malformed:
                with self.subTest(malformed=body[:24]):
                    compare(packet(state, body), 'input')
            exact = request(proof='x'*(32768-len(request(proof=''))))
            self.assertEqual(len(exact), 32768)
            self.assertEqual(compare(packet(state, exact))[0], 1)
            compare(packet(state, exact+b'\0'), 'limit')
            # Private transport failures remain private failures. They cannot
            # be misreported as an invalid client credential.
            for incoming in (b'', b'\0'*7, packet(b'\0', request()),
                             packet(b'x'*65537, request()),
                             (len(state)+100).to_bytes(8, 'big')+state):
                self.assertEqual(compare(incoming), b'\2')

            # Real service dispatch still authenticates before proof admission
            # and prepared-handle/proof validation. Malformed envelopes win.
            for operation in (None, 0, 1, 2):
                with self.subTest(operation=operation):
                    message = frame({'code': 'absent', 'proof': 'bad', 'credential': 'invalid', 'arguments': None}) \
                        if operation is None else prepared_frame(operation, 'absent', 'invalid', proof='bad')
                    self.assertEqual(server.exchange(message), {'status': 'authentication', 'value': None})
                    body = (b'' if operation is None else bytes((7, operation)))+encode({'credential': 'invalid'})
                    self.assertEqual(server.exchange(len(body).to_bytes(8, 'big')+body),
                                     {'status': 'input', 'value': None})
            for operation in (1, 2):
                self.assertEqual(server.prepared(operation, 'absent', 'alice-token', proof='bad'),
                                 {'status': 'input', 'value': None})
                self.assertEqual(server.prepared(operation, 'absent', 'alice-token'),
                                 {'status': 'failure', 'value': None})
            self.assertEqual(server.call('bad code', 'bad proof', 'alice-token'),
                             {'status': 'certificate', 'value': None})
            code, proof = ((ROOT/'examples/access'/name).read_text() for name in ('Client.bend', 'ClientProof.bend'))
            self.assertEqual(server.call(code, proof, 'alice-token', 'current-token'),
                             {'status': 'success', 'value': 'current-token'}, server.diagnostics())
            self.assertEqual(server.call(code, proof, 'alice-token'), {'status': 'authentication', 'value': None})
            self.assertEqual(server.call(code, proof, 'current-token'), {'status': 'refusal', 'value': 'cancelled'})
            # The full extension fits exactly (and is malformed inside). One
            # extra byte is rejected from its header without reading any body.
            body = bytes((7, 1))+b'\0'*32766
            self.assertEqual(server.exchange(len(body).to_bytes(8, 'big')+body),
                             {'status': 'input', 'value': None})
            self.assertEqual(server.exchange((32769).to_bytes(8, 'big')),
                             {'status': 'limit', 'value': None})
            server.finish()
            if trace:
                launches = [line for line in Path(trace).read_text().splitlines()
                            if 'execve(' in line and '.program"' in line and '= 0' in line]
                counts = {'initialize': 0, 'authenticate': 0, 'execute': 0}
                for line in launches:
                    self.assertNotIn('/decode/', line)
                    key = 'authenticate' if '/authenticate/' in line else 'initialize' if '/initialize/' in line else 'execute'
                    counts[key] += 1
                self.assertEqual(counts, {'initialize': 1, 'authenticate': 18, 'execute': 2})
                print('host native launches: '+json.dumps(counts), flush=True)


if __name__ == '__main__':
    unittest.main(verbosity=2)
