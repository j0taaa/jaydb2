#!/usr/bin/env python3
"""Actual ABI6 initialization rejects another environment identity."""
from pathlib import Path
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.bootstrap import LOCK
from tools.service import staging
from tools.service.controller import build
from tools.service.entry import prepare_entry
from tests.service.observation import fixture_loading


class InitializationIdentity(unittest.TestCase):
    def test_structurally_valid_configuration_cannot_name_another_environment(self):
        prepare_entry()
        with tempfile.TemporaryDirectory(prefix='jaydb-initialization-identity-') as temp:
            root = Path(temp)
            config = root / 'administrator'
            config.mkdir()
            original = ROOT / 'examples/credenciais'
            (config / 'Seed.bend').write_bytes((original / 'Seed.bend').read_bytes())
            source = (original / 'Configuration.bend').read_text()
            self.assertEqual(source.count('E.identidade()'), 1)
            (config / 'Configuration.bend').write_text(source.replace('E.identidade()', '"outro-ambiente"'))
            environment = staging.Environment(config / 'Configuration.bend', config / 'Seed.bend')
            runtime = environment.materialize_tooling(root / 'runtime')
            request = root / 'initialization'
            request.mkdir()
            toolchain = (ROOT / '.tools' / ('bend-source-' + LOCK['version']),
                         ROOT / '.tools' / ('bendtt-' + LOCK['kernelSha256']))
            module, limits = build(environment, request, 'initialize', toolchain,
                tools_root=runtime,
                loading_runtime=fixture_loading())
            try:
                self.assertEqual(set(limits), {'mensagem', 'estado', 'resposta'})
                self.assertTrue(module.report['simpleABI6'])
                self.assertEqual(module.run(b'', capacity=limits['estado'] + 1), b'\2')
            finally:
                module.close()


if __name__ == '__main__':
    unittest.main(verbosity=2)
