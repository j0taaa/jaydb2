"""Profile integrity: distinct metadata, real preparation modes, restored globals."""
import copy
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock, patch

import optimized


class ProfileTests(unittest.TestCase):
    def test_running_successful_and_failed_root_manifests_are_labelled_before_save(self):
        for status in ('running', 'passed', 'failed'):
            with self.subTest(status=status):
                samples = [{'elapsed_ns': 123, 'checked': True}]
                manifest = {'status': status, 'settings': {'samples': 7, 'durable': True},
                            'results': [{'samples': copy.deepcopy(samples)}]}
                saved = Mock()
                optimized.profile_save(saved, Path('result.json'), manifest)
                saved.assert_called_once_with(Path('result.json'), manifest)
                self.assertEqual(manifest['settings']['profile'], 'single-call-queries-v1')
                self.assertEqual(manifest['settings']['profile_metadata'], optimized.PROFILE_METADATA)
                self.assertEqual(manifest['status'], status)
                self.assertEqual(manifest['settings']['samples'], 7)
                self.assertIs(manifest['settings']['durable'], True)
                self.assertEqual(manifest['results'], [{'samples': samples}])

    def test_engine_records_and_sql_settings_are_not_relabelled(self):
        record = {'settings': {'fsync': 'on'}, 'samples': [], 'status': 'passed'}
        before = copy.deepcopy(record)
        saved = Mock()
        optimized.profile_save(saved, Path('postgresql/result.json'), record)
        saved.assert_called_once()
        self.assertEqual(record, before)

    def test_preparation_registers_each_program_once_in_its_actual_mode(self):
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            for name, depth in (('Access', 2), ('Batch', 3), ('ReadRow', 7)):
                (folder/f'{name}.bend').write_bytes((optimized.HERE.parent/f'{name}.bend').read_bytes())
                (folder/f'{name}Proof.bend').write_text(optimized.base.proof(depth))
            for source, target in (('Read', 'Reader'), ('Sum', 'Sum'), ('Join', 'Join')):
                for suffix in ('', 'Proof'):
                    (folder/f'{target}{suffix}.bend').write_bytes((optimized.HERE/f'{source}{suffix}.bend').read_bytes())
            database = optimized.OptimizedJay.__new__(optimized.OptimizedJay)
            database.folder, database.handles, database.setup = folder, {'stale': 'old'}, {'startup_ns': 1}
            database.exchange = Mock(side_effect=[{'status': 'prepared', 'value': str(i)} for i in range(6)])
            database.prepare()
            self.assertEqual(database.exchange.call_count, 6)
            self.assertEqual([call.args[0] for call in database.exchange.call_args_list], [0, 0, 3, 3, 0, 0])
            self.assertEqual(set(database.handles), {name for name, opcode in optimized.PROGRAMS})
            self.assertEqual(len([call for call in database.exchange.call_args_list
                                  if call.args[1] == (folder/'ReadRow.bend').read_text()]), 1)
            self.assertEqual((folder/'ReadRowProof.bend').read_text(), optimized.read_row_proof())
            self.assertEqual(database.setup['startup_ns'], 1)
            self.assertTrue(all(database.setup[f'prepare_{name.lower()}_ns'] > 0 for name, _ in optimized.PROGRAMS))

    def test_each_optimized_public_query_uses_one_service_call(self):
        database = optimized.OptimizedJay.__new__(optimized.OptimizedJay)
        database.execute = Mock(return_value='real-adapter-result')
        cases = [(lambda: database.get('items', 'k9', 'amount'), ['read', 'items', 'k9', 'amount'], 'Reader'),
                 (lambda: database.keys('items'), ['keys', 'items'], 'Reader'),
                 (lambda: database.aggregate('items', 'amount'), ['sum', 'items', 'amount'], 'Sum'),
                 (lambda: database.join({'from_table': 'lines', 'fk': 'item_id', 'to_table': 'items', 'column': 'name'}),
                  ['join', 'lines', 'item_id', 'items', 'name'], 'Join')]
        for invoke, arguments, handle in cases:
            database.execute.reset_mock()
            self.assertEqual(invoke(), 'real-adapter-result')
            database.execute.assert_called_once_with(arguments, handle)

    def test_entrypoint_restores_legacy_globals_when_runner_raises(self):
        previous_jay, previous_save = optimized.legacy.Jay, optimized.legacy.save
        with patch.object(optimized.legacy, 'main', side_effect=RuntimeError('controlled failure')):
            with self.assertRaisesRegex(RuntimeError, 'controlled failure'):
                optimized.main()
        self.assertIs(optimized.legacy.Jay, previous_jay)
        self.assertIs(optimized.legacy.save, previous_save)


if __name__ == '__main__':
    unittest.main()
