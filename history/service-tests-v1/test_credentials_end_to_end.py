"""Real transactions, provisional credentials, publication and rollback."""
from pathlib import Path
import os
import shutil
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.bootstrap import LOCK
from tools.client import encode, frame, unframe
from tools.service.staging import Environment
from tests.service.observation import PublicationObservedDatabase,fixture_loading


class CredentialTransactions(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.folder = ROOT / 'examples/credenciais'
        cls.temporary = tempfile.TemporaryDirectory(prefix='jaydb-kernel-test-')
        cls.kernel = Path(cls.temporary.name) / 'bendtt'
        shutil.copyfile(ROOT / '.tools' / ('bendtt-' + LOCK['kernelSha256']), cls.kernel)
        cls.kernel.chmod(0o700)
        cls.db = PublicationObservedDatabase(Environment(cls.folder / 'Configuration.bend', cls.folder / 'Seed.bend'),
            (ROOT / '.tools' / ('bend-source-' + LOCK['version']), cls.kernel),loading_runtime=fixture_loading())

    @classmethod
    def tearDownClass(cls):
        cls.db.close()
        cls.temporary.cleanup()

    def call(self, credential='demo', value='nova', code=None):
        code = (self.folder / 'Client.bend').read_bytes().decode() if code is None else code
        proof = (self.folder / 'ClientProof.bend').read_bytes().decode()
        assignments = self.db.root_assignments
        result = unframe(self.db.request(encode({'codigo': code, 'prova': proof,
            'credencial': credential, 'argumentos': value})))
        self.assertEqual(self.db.root_assignments - assignments, int(result['status'] == 'sucesso'))
        return result

    def test_01_empty_at_publication_is_dados_and_rolls_back(self):
        initial = self.db.state
        self.assertEqual(self.call(value=''), {'status': 'dados', 'valor': None}, self.db.last_failure)
        self.assertEqual(self.db.state, initial)

    def test_02_provisional_empty_repaired_and_read_own_write(self):
        initial = self.db.state
        self.assertEqual(self.call(), {'status': 'sucesso', 'valor': 'nova'}, self.db.last_failure)
        self.assertNotEqual(self.db.state, initial)

    def test_03_previous_credential_stops_authenticating(self):
        state = self.db.state
        self.assertEqual(self.call(), {'status': 'autenticacao', 'valor': None})
        self.assertEqual(self.db.state, state)

    def test_04_next_call_uses_exact_published_state(self):
        self.assertEqual(self.call('nova', 'nova2'), {'status': 'sucesso', 'valor': 'nova2'}, self.db.last_failure)

    def test_05_refusal_discards_mutations_but_keeps_observed_payload(self):
        state = self.db.state
        code = (self.folder / 'Client.bend').read_text().replace('S.Terminar{valor}', 'S.Recusar{valor}')
        self.assertEqual(self.call('nova2', 'temporaria', code), {'status': 'recusa', 'valor': 'temporaria'}, self.db.last_failure)
        self.assertEqual(self.db.state, state)

    def test_06_invalid_write_is_dados_and_discards_provisional_empty(self):
        state = self.db.state
        code = (self.folder / 'Client.bend').read_text().replace('token(args)', 'D.VInt{0, 1}')
        self.assertEqual(self.call('nova2', code=code), {'status': 'dados', 'valor': None}, self.db.last_failure)
        self.assertEqual(self.db.state, state)

    def echo(self, argument):
        assignments = self.db.root_assignments
        result = unframe(self.db.request(encode({
            'codigo': (self.folder / 'Eco.bend').read_bytes().decode(),
            'prova': (self.folder / 'EcoProof.bend').read_bytes().decode(),
            'credencial': 'nova2', 'argumentos': argument})))
        self.assertEqual(self.db.root_assignments - assignments, int(result['status'] == 'sucesso'))
        self.assertEqual(result['status'], 'sucesso', self.db.last_failure)
        # Canonical encoding is iterative, so comparison adds no Python depth cap.
        self.assertEqual(encode(result['valor']), encode(argument))

    def test_06a_large_text_argument_is_reified_exactly(self):
        self.echo('x' * 10000)

    def test_06b_unicode_and_controls_argument_is_reified_exactly(self):
        self.echo(('\0\x01\t\r\n"\\\u00ff\U0001f600' * 500))

    def test_06c_deep_argument_is_reified_without_nested_source_ast(self):
        argument = -9223372036854775808
        # 2500 levels reached the real 30s framing deadline on the test host.
        # This case checks value fidelity within that budget; src has no depth cap.
        for _ in range(768):
            argument = [argument]
        self.echo(argument)

    def test_07_delivery_failure_after_publication_does_not_roll_back(self):
        r, w = os.pipe()
        output_r, output_w = os.pipe()
        try:
            request = frame({'codigo': (self.folder / 'Client.bend').read_bytes().decode(),
                'prova': (self.folder / 'ClientProof.bend').read_bytes().decode(),
                'credencial': 'nova2', 'argumentos': 'apos_entrega'})
            os.write(w, request)
            os.close(w)
            w = None
            os.close(output_r)
            output_r = None
            state = self.db.state
            assignments = self.db.root_assignments
            with self.assertRaises(BrokenPipeError):
                self.db.serve(r, output_w)
            self.assertNotEqual(self.db.state, state)
            self.assertEqual(self.db.root_assignments - assignments, 1)
        finally:
            for fd in (r, w, output_r, output_w):
                if fd is not None:
                    os.close(fd)

    def test_08_oversized_header_is_limite_and_closes_channel(self):
        r, w = os.pipe()
        output_r, output_w = os.pipe()
        try:
            os.write(w, (self.db.limits['mensagem'] + 1).to_bytes(8, 'big'))
            os.close(w)
            w = None
            state = self.db.state
            assignments = self.db.root_assignments
            self.db.serve(r, output_w)
            os.close(output_w)
            output_w = None
            response = os.read(output_r, 1024)
            self.assertEqual(unframe(response), {'status': 'limite', 'valor': None})
            self.assertEqual(os.read(output_r, 1), b'')
            self.assertEqual(self.db.state, state)
            self.assertEqual(self.db.root_assignments, assignments)
        finally:
            for fd in (r, w, output_r, output_w):
                if fd is not None:
                    os.close(fd)

    def test_09_real_missing_verifier_is_falha_and_rolls_back(self):
        state = self.db.state
        self.kernel.unlink()
        self.assertEqual(self.call('apos_entrega'), {'status': 'falha', 'valor': None}, self.db.last_failure)
        self.assertEqual(self.db.state, state)


if __name__ == '__main__':
    unittest.main(verbosity=2)
