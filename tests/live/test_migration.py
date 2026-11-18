"""Exercise checked whole-state migrations with the pinned native toolchain."""

from copy import deepcopy
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from applications.tasks.app import prepare
from tools.client import decode, encode, unframe


ROOT = Path(__file__).resolve().parents[2]
EXAMPLE = ROOT / 'applications/tasks/migrations'
LOCK = json.loads((ROOT / 'tools/admission/toolchain.lock.json').read_text())
TOOLCHAIN = (
    ROOT / '.tools' / ('bend-source-' + LOCK['version']),
    ROOT / '.tools' / ('bendtt-' + LOCK['kernelSha256']),
)
OLD_STATE = {
    'tables': [
        {'name': 'alice', 'rows': [
            {'completed': False, 'id': 'a1', 'owner': 'alice', 'title': 'Buy bread'},
            {'completed': True, 'id': 'a2', 'owner': 'alice', 'title': 'Call Zoë'},
        ]},
        {'name': 'bob', 'rows': [
            {'completed': False, 'id': 'b1', 'owner': 'bob', 'title': 'Review report'},
        ]},
    ],
    'users': [
        {'credential': 'alice-token', 'id': 'alice', 'kind': 'user'},
        {'credential': 'bob-token', 'id': 'bob', 'kind': 'user'},
    ],
}


class MigrationTest(unittest.TestCase):
    def setUp(self):
        scratch = tempfile.TemporaryDirectory(prefix='jaydb-migrate-')
        self.addCleanup(scratch.cleanup)
        self.root = Path(scratch.name)
        old = self.root / 'old-app'
        new = self.root / 'new-app'
        for folder in (old, new):
            folder.mkdir()
            prepare(folder)
        # The two administrator graphs may reuse a helper filename with different bytes.
        policy = new / 'Policy.bend'
        policy.write_text(policy.read_text() + '\ndef version() -> Nat:\n  2n\n')
        self.old = old / 'Configuration.bend'
        self.new = new / 'Configuration.bend'
        self.new.write_bytes((EXAMPLE / 'Configuration.bend').read_bytes())
        self.migration = (EXAMPLE / 'Migration.bend').read_text()

    def build(self, name, source, *, old=None):
        module = self.root / (name + '.bend')
        module.write_text(source)
        output = self.root / name
        result = subprocess.run(
            ['node', '--stack_size=65536', 'tools/service/stage.mjs', 'migrate',
             output, old or self.old, self.new, module, *TOOLCHAIN],
            cwd=ROOT, capture_output=True, text=True, timeout=180,
        )
        return result, output / 'migrate'

    def admitted(self, name, source, *, old=None):
        result, artifact = self.build(name, source, old=old)
        self.assertEqual(result.returncode, 0, result.stderr)
        report = json.loads((artifact / 'checked.c.json').read_text())['admission']
        self.assertTrue(report['primary'])
        self.assertTrue(report['bendtt'])
        self.assertEqual(report['kernel']['primitives'], ['Native:read', 'Native:write'])
        return json.loads(result.stdout), artifact

    def run_migration(self, program, canonical_state):
        result = subprocess.run(
            [program, '+RTS', '--threads', '1', '--gpu', 'off', '-RTS'],
            cwd=ROOT, input=canonical_state, capture_output=True, timeout=20,
            env={**os.environ, 'BENDRTS': ''},
        )
        self.assertEqual(result.returncode, 0, result.stderr)
        return result.stdout

    def test_rows_are_preserved_and_decode_under_new_schema(self):
        built, artifact = self.admitted('success', self.migration)
        self.assertIn('def version()', (artifact / 'Policy.bend').read_text())
        self.assertNotIn('def version()', (artifact / 'Old/Policy.bend').read_text())

        expected = deepcopy(OLD_STATE)
        for table in expected['tables']:
            for row in table['rows']:
                row['priority'] = None
        result = self.run_migration(built['program'], encode(OLD_STATE))
        self.assertEqual(result[:1], b'\x01')
        self.assertEqual(decode(result[1:]), expected)
        self.assertEqual(result[1:], encode(expected))
        self.assert_error(self.run_migration(built['program'], result[1:]), 'failure')

        # Feed the proposal back through the checked decoder using the frozen
        # new environment. Use a ceiling equal to the canonical proposal size.
        self.new.write_text(self.new.read_text().replace('65536n', f'{len(result) - 1}n').replace(
            'Policy.config(schema(), limits(), environment())',
            'S.Configuration{schema(), S.NoneLaw{}, limits(), environment()}',
        ))
        identity = '''import Base
import ./Data.bend as D
import ./Requirements.bend as R
import ./Old/Configuration.bend as Old

def migrate(s: D.State) -> D.State:
  s

def preserves(s: D.State, valid: R.Valid(Old.config(), s)) -> Unit:
  Unit{}
'''
        checked, _ = self.admitted('redecode', identity, old=built['newEnvironment'])
        self.assertEqual(self.run_migration(checked['program'], result[1:]), result)

        expected['tables'][0]['rows'][0]['title'] += '!'
        self.assert_error(self.run_migration(checked['program'], encode(expected)), 'limit')

    def assert_error(self, result, status):
        self.assertEqual(result[:1], b'\x00')
        self.assertEqual(unframe(result[1:]), {'status': status, 'value': None})

    def test_bad_structure_is_rejected_after_admission(self):
        invalid = self.migration.replace('D.Field{"priority", D.VAbsent{}}',
                                         'D.Field{"priority", D.VBool{True{}}}')
        built, _ = self.admitted('bad-structure', invalid)
        self.assert_error(self.run_migration(built['program'], encode(OLD_STATE)), 'data')

    def test_invalid_proof_is_rejected_at_admission(self):
        invalid = self.migration[:self.migration.index('law preserves:')] + '''
def preserves(s: D.State, valid: R.Valid(Old.config(), s)) -> Unit:
  Unit{}
'''
        result, artifact = self.build('bad-proof', invalid)
        self.assertEqual(result.returncode, 2)
        self.assertIn('"code":"PRIMARY_CHECK"', result.stderr)
        self.assertIn('migration_preserves_laws', result.stderr)
        self.assertFalse(list(artifact.glob('*.program')))


if __name__ == '__main__':
    unittest.main()
