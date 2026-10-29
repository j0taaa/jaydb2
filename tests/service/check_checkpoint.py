#!/usr/bin/env python3
"""Run the real service against one frozen native backend checkpoint."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys
import tarfile
import tempfile
import time
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.service import staging
from tests.service import test_end_to_end as main
from tests.service import test_credentials_end_to_end as credentials
from tests.service import test_swap_end_to_end as swap


def digest(data):
    return hashlib.sha256(data).hexdigest()


def run():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checkpoint', type=Path, default=ROOT / 'tests/native/checkpoints/v3_owned.tar.gz')
    parser.add_argument('--record', type=Path, default=ROOT / 'tests/service/V3_INTEGRATION.json')
    parser.add_argument('--pattern', action='append', help='Optional unittest name glob; repeat to select affected cases')
    args = parser.parse_args()
    checkpoint = args.checkpoint.resolve()
    report = {'startedAt': datetime.now(timezone.utc).isoformat(),
              'backendCheckpoint': str(checkpoint.relative_to(ROOT)),
              'backendCheckpointSha256': digest(checkpoint.read_bytes()),
              'fullExecutableContractProved': False}
    host_paths = [*(ROOT / 'tools/service').glob('*.py'), Path(__file__),
                  Path(main.__file__), Path(credentials.__file__), Path(swap.__file__),
                  ROOT / 'tests/service/observation.py']
    host_hashes = {str(p.relative_to(ROOT)): digest(p.read_bytes()) for p in host_paths}
    with tempfile.TemporaryDirectory(prefix='jaydb-service-checkpoint-') as temp:
        root = Path(temp)
        with tarfile.open(checkpoint) as archive:
            archive.extractall(root, filter='data')
        for name in ('contrato', 'src', 'tools/admission', 'tools/verifier', 'tools/service',
                     'tools/accounting', 'native/accounting'):
            (root / name).symlink_to(ROOT / name, target_is_directory=True)
        for name in ('jaydb2.py', 'tools/bootstrap.py'):
            (root / name).symlink_to(ROOT / name)
        environments = {}
        try:
            staging.ROOT = root
            for module, name in ((main, 'sem-observacoes'), (credentials, 'credenciais'), (swap, 'troca-credenciais')):
                folder = ROOT / 'examples' / name
                env = staging.Environment(folder / 'Configuration.bend', folder / 'Seed.bend')
                environments[name] = env
                module.Environment = lambda config, seed, frozen=env: frozen
        finally:
            staging.ROOT = ROOT
        report['environments'] = {name: env.identity for name, env in environments.items()}
        report['toolingSha256'] = {name: digest(data)
            for name, data in environments['sem-observacoes'].tooling.items()}
        report['publicSourcesSha256'] = {name: {path: digest(data) for path, data in env.sources.items()}
            for name, env in environments.items()}
        loader = unittest.TestLoader()
        loader.testNamePatterns = args.pattern
        suite = unittest.TestSuite(loader.loadTestsFromTestCase(case)
            for case in (main.EndToEndTests, credentials.CredentialTransactions, swap.CredentialExchange))
        report['selectedPatterns'] = args.pattern
        start = time.monotonic()
        result = unittest.TextTestRunner(verbosity=2).run(suite)
        report.update(tests=result.testsRun, failures=len(result.failures), errors=len(result.errors),
                      durationSeconds=round(time.monotonic() - start, 3))
    report['hostSourcesUnchanged'] = host_hashes == {str(p.relative_to(ROOT)): digest(p.read_bytes()) for p in host_paths}
    report['hostSourcesSha256'] = host_hashes
    args.record.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n')
    return 0 if result.wasSuccessful() and report['hostSourcesUnchanged'] else 1


if __name__ == '__main__':
    raise SystemExit(run())
