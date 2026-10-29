#!/usr/bin/env python3
"""Real checked initialization rejects a configuration naming another environment.

The native backend is frozen while its next revision is under development.
All admission, proof checking, staging and configuration checks are production.
"""
from pathlib import Path
import sys
import tarfile
import tempfile
import time
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.bootstrap import LOCK
from tools.service import staging
from tools.service.controller import build
from tests.service.observation import fixture_loading


class InitializationIdentity(unittest.TestCase):
    def test_structurally_valid_configuration_cannot_name_another_environment(self):
        with tempfile.TemporaryDirectory(prefix='jaydb-initialization-identity-') as temp:
            root = Path(temp)
            with tarfile.open(ROOT / 'tests/native/checkpoints/v3_owned.tar.gz') as archive:
                archive.extractall(root, filter='data')
            for name in ('contrato', 'src', 'tools/admission', 'tools/verifier', 'tools/service'):
                (root / name).symlink_to(ROOT / name, target_is_directory=True)
            for name in ('jaydb2.py', 'tools/bootstrap.py'):
                (root / name).symlink_to(ROOT / name)
            config = root / 'administrator'
            config.mkdir()
            original = ROOT / 'examples/credenciais'
            (config / 'Seed.bend').write_bytes((original / 'Seed.bend').read_bytes())
            source = (original / 'Configuration.bend').read_text()
            self.assertEqual(source.count('E.identidade()'), 1)
            (config / 'Configuration.bend').write_text(source.replace('E.identidade()', '"outro-ambiente"'))
            try:
                staging.ROOT = root
                environment = staging.Environment(config / 'Configuration.bend', config / 'Seed.bend')
            finally:
                staging.ROOT = ROOT
            runtime = environment.materialize_tooling(root / 'runtime')
            request = root / 'initialization'
            request.mkdir()
            toolchain = (ROOT / '.tools' / ('bend-source-' + LOCK['version']),
                         ROOT / '.tools' / ('bendtt-' + LOCK['kernelSha256']))
            module, limits = build(environment, request, 'initialize', toolchain,
                deadline=time.monotonic_ns() + 120 * 10**9, memory=4 * 1024**3, tools_root=runtime,
                loading_runtime=fixture_loading())
            try:
                self.assertEqual(module.run(b'', capacity=limits['estado'] + 1,
                    memory=limits['memoria'], timeout_ns=10**10), b'\2')
            finally:
                module.close()


if __name__ == '__main__':
    unittest.main(verbosity=2)
