"""Real admission, compilation, same-process CPU execution and wire response."""
from pathlib import Path
import os
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.bootstrap import LOCK
from tools.client import encode, frame, unframe
from tools.service.staging import Environment
from tests.service.observation import PublicationObservedDatabase,fixture_loading


class EndToEndTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        folder = ROOT / 'examples/sem-observacoes'
        cls.folder = folder
        tc = (ROOT / '.tools' / ('bend-source-' + LOCK['version']),
              ROOT / '.tools' / ('bendtt-' + LOCK['kernelSha256']))
        cls.db = PublicationObservedDatabase(Environment(folder / 'Configuration.bend', folder / 'Seed.bend'), tc,
                                             loading_runtime=fixture_loading())
        cls.initial = cls.db.state

    @classmethod
    def tearDownClass(cls):
        cls.db.close()

    def call(self, code=None, proof=None, credential='demo'):
        code = (self.folder / 'Client.bend').read_bytes().decode() if code is None else code
        proof = (self.folder / 'ClientProof.bend').read_bytes().decode() if proof is None else proof
        assignments = self.db.root_assignments
        result = unframe(self.db.request(encode({'codigo': code, 'prova': proof,
            'credencial': credential, 'argumentos': None})))
        self.assertEqual(self.db.root_assignments - assignments, int(result['status'] == 'sucesso'))
        return result

    def tearDown(self):
        self.assertEqual(self.db.state, self.initial)

    def test_01_malformed_body_is_entrada(self):
        self.assertEqual(unframe(self.db.request(b'\xff')), {'status': 'entrada', 'valor': None})

    def test_01a_impossible_internal_lengths_are_entrada(self):
        # The complete outer body has only nine bytes. Its impossible inner
        # lengths are malformed input, without an actual exhausted resource.
        for tag in (4, 5, 6):
            with self.subTest(tag=tag):
                body = bytes([tag]) + (2**64 - 1).to_bytes(8, 'big')
                self.assertEqual(unframe(self.db.request(body)), {'status': 'entrada', 'valor': None})

    def test_02_authentication_precedes_invalid_source_and_proof(self):
        for credential in ('', 'invalid'):
            self.assertEqual(self.call('invalid source', '?invalid', credential),
                             {'status': 'autenticacao', 'valor': None})

    def test_03_missing_certificate(self):
        self.assertEqual(self.call(proof=''), {'status': 'certificado', 'valor': None})

    def test_04_pure_recursive_refusal(self):
        self.assertEqual(self.call(), {'status': 'recusa', 'valor': 6}, self.db.last_failure)

    def test_05_changed_program_cannot_reuse_termination_proof(self):
        code = (self.folder / 'Client.bend').read_text().replace('[1, 2, 3]', '[1, 2, 4]')
        self.assertEqual(self.call(code=code), {'status': 'certificado', 'valor': None})

    def test_06_no_external_io_even_in_unused_definition(self):
        code = (self.folder / 'Client.bend').read_text() + '\ndef hidden() -> IO(Unit):\n  IO.exit(91)\n'
        self.assertEqual(self.call(code=code), {'status': 'certificado', 'valor': None})

    def test_06a_import_cycle_is_a_certificate_error(self):
        code = 'import ./Client.bend as Self\n' + (self.folder / 'Client.bend').read_text()
        self.assertEqual(self.call(code=code), {'status': 'certificado', 'valor': None})

    def test_07_control_characters_preserved_by_generated_source_literal(self):
        code = (self.folder / 'Client.bend').read_bytes().decode() + '# Unicode \U0001f600 and controls: \0\x01\t\r\n'
        self.assertEqual(self.call(code=code), {'status': 'recusa', 'valor': 6}, self.db.last_failure)

    def test_08_certified_success(self):
        code = (self.folder / 'Sucesso.bend').read_bytes().decode()
        proof = (self.folder / 'SucessoProof.bend').read_bytes().decode()
        self.assertEqual(self.call(code, proof), {'status': 'sucesso', 'valor': 6}, self.db.last_failure)

    def stream(self, data):
        r, w = os.pipe()
        try:
            os.write(w, data)
            os.close(w)
            w = None
            assignments = self.db.root_assignments
            with tempfile.TemporaryFile() as output:
                self.db.serve(r, output.fileno())
                output.seek(0)
                response = output.read()
            self.assertEqual(self.db.root_assignments, assignments)
            return response
        finally:
            os.close(r)
            if w is not None:
                os.close(w)

    def test_09_complete_malformed_body_preserves_next_frame(self):
        data = ((1).to_bytes(8, 'big') + b'\xff' + frame({'codigo': 'bad source',
            'prova': 'bad proof', 'credencial': 'invalid', 'argumentos': None}))
        response = self.stream(data)
        first = 8 + int.from_bytes(response[:8], 'big')
        self.assertEqual(unframe(response[:first]), {'status': 'entrada', 'valor': None})
        self.assertEqual(unframe(response[first:]), {'status': 'autenticacao', 'valor': None})

    def test_10_eof_between_messages_has_no_response(self):
        self.assertEqual(self.stream(b''), b'')

    def test_10a_impossible_inner_length_keeps_next_frame(self):
        body = b'\4' + (2**64 - 1).to_bytes(8, 'big')
        following = frame({'codigo': 'bad source', 'prova': 'bad proof',
            'credencial': 'invalid', 'argumentos': None})
        response = self.stream(len(body).to_bytes(8, 'big') + body + following)
        first = 8 + int.from_bytes(response[:8], 'big')
        self.assertEqual(unframe(response[:first]), {'status': 'entrada', 'valor': None})
        self.assertEqual(unframe(response[first:]), {'status': 'autenticacao', 'valor': None})

    def test_11_incomplete_frame_returns_entrada_and_closes(self):
        for incomplete in (b'\0', b'\0' * 7, (8).to_bytes(8, 'big') + b'\4\0\0'):
            with self.subTest(size=len(incomplete)):
                self.assertEqual(unframe(self.stream(incomplete)), {'status': 'entrada', 'valor': None})


if __name__ == '__main__':
    unittest.main(verbosity=2)
