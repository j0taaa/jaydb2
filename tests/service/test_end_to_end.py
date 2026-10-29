"""Real admission -> emitted C -> ABI -> publication, with current examples."""
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from tools.bootstrap import LOCK
from tools.client import encode, unframe
from tools.service.controller import Database, build
from tools.service.entry import prepare_entry
from tools.service.staging import Environment

ROOT = Path(__file__).resolve().parents[2]
TOOLCHAIN = (ROOT/'.tools'/('bend-source-'+LOCK['version']),
             ROOT/'.tools'/('bendtt-'+LOCK['kernelSha256']))


class EndToEndTests(unittest.TestCase):
    def test_transaction_rollback_publication_and_authenticated_identity(self):
        # The invalid final duplicate rolls back; a valid exchange publishes
        # once, keeps the caller's identity, and changes the next authentication.
        folder = ROOT/'examples/troca-credenciais'
        db = Database(Environment(folder/'Configuration.bend', folder/'Seed.bend'), TOOLCHAIN)
        self.addCleanup(db.close)
        def call(credential, arguments=None, who=False):
            source, proof = ('Quem', 'QuemProof') if who else ('Client', 'ClientProof')
            with patch.object(db, '_publish', wraps=db._publish) as publish:
                answer = unframe(db.request(encode({
                    'codigo': (folder/(source+'.bend')).read_text(),
                    'prova': (folder/(proof+'.bend')).read_text(),
                    'credencial': credential, 'argumentos': arguments})))
            self.assertEqual(publish.call_count, int(answer['status'] == 'sucesso'))
            return answer
        initial = db.state
        self.assertEqual(call('alice-token', ['same', 'same']),
                         {'status': 'dados', 'valor': None}, db.last_failure)
        self.assertEqual(db.state, initial)
        self.assertEqual(call('alice-token'), {'status': 'sucesso', 'valor': 'bob-token'}, db.last_failure)
        self.assertNotEqual(db.state, initial)
        self.assertEqual(call('alice-token', who=True), {'status': 'sucesso', 'valor': 'bob'}, db.last_failure)

    def test_initialization_rejects_another_environment_identity(self):
        # A structurally valid configuration cannot claim a different runtime.
        prepare_entry()
        with tempfile.TemporaryDirectory(prefix='jaydb-identity-test-') as temporary:
            root = Path(temporary)
            original = ROOT/'examples/credenciais'
            (root/'Seed.bend').write_bytes((original/'Seed.bend').read_bytes())
            source = (original/'Configuration.bend').read_text()
            self.assertEqual(source.count('E.identidade()'), 1)
            (root/'Configuration.bend').write_text(source.replace('E.identidade()', '"other-environment"'))
            environment = Environment(root/'Configuration.bend', root/'Seed.bend')
            runtime = environment.materialize_tooling(root/'runtime')
            stage = root/'initialize'
            stage.mkdir()
            module, limits = build(environment, stage, 'initialize', TOOLCHAIN, tools_root=runtime)
            with module:
                self.assertEqual(set(limits), {'mensagem', 'estado', 'resposta'})
                self.assertEqual(module.run(b'', capacity=limits['estado']+1), b'\2')


if __name__ == '__main__':
    unittest.main(verbosity=2)
