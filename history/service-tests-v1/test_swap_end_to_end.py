"""Atomic exchange of two credentials, including stable request identity."""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.bootstrap import LOCK
from tools.client import encode, unframe
from tools.service.staging import Environment
from tests.service.observation import PublicationObservedDatabase,fixture_loading


class CredentialExchange(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.folder = ROOT / 'examples/troca-credenciais'
        cls.db = PublicationObservedDatabase(
            Environment(cls.folder / 'Configuration.bend', cls.folder / 'Seed.bend'),
            (ROOT / '.tools' / ('bend-source-' + LOCK['version']),
             ROOT / '.tools' / ('bendtt-' + LOCK['kernelSha256'])),loading_runtime=fixture_loading())

    @classmethod
    def tearDownClass(cls):
        cls.db.close()

    def call(self, credential, *, who=False, arguments=None):
        source, proof = ('Quem.bend', 'QuemProof.bend') if who else ('Client.bend', 'ClientProof.bend')
        assignments = self.db.root_assignments
        result = unframe(self.db.request(encode({
            'codigo': (self.folder / source).read_bytes().decode(),
            'prova': (self.folder / proof).read_bytes().decode(),
            'credencial': credential, 'argumentos': arguments})))
        self.assertEqual(self.db.root_assignments - assignments, int(result['status'] == 'sucesso'))
        return result

    def test_exchange_keeps_authenticated_identity_then_updates_next_call(self):
        initial = self.db.state
        # The first write duplicates bob-token. Publication is valid only after
        # the second write completes the exchange. The current caller is Alice.
        self.assertEqual(self.call('alice-token'), {'status': 'sucesso', 'valor': 'bob-token'}, self.db.last_failure)
        self.assertNotEqual(self.db.state, initial)
        self.assertEqual(self.call('alice-token', who=True), {'status': 'sucesso', 'valor': 'bob'}, self.db.last_failure)
        self.assertEqual(self.call('bob-token', who=True), {'status': 'sucesso', 'valor': 'alice'}, self.db.last_failure)
        exchanged = self.db.state
        # Keeping both credentials equal at the end cannot publish.
        self.assertEqual(self.call('bob-token', arguments=['same', 'same']),
                         {'status': 'dados', 'valor': None}, self.db.last_failure)
        self.assertEqual(self.db.state, exchanged)


if __name__ == '__main__':
    unittest.main(verbosity=2)
