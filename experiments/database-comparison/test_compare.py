"""Lightweight tests of result fidelity and honest paired comparison gates."""
import copy
import json
from pathlib import Path
import statistics
import tempfile
import unittest

import compare
import model
from run import check


def fixture():
    settings = {'samples': 3, 'warmups': 1, 'engines': ['jaydb2'], 'durable': True,
                'clients': 1, 'jay_threads': 1, 'read_workers': 1,
                'result_equality': 'recursive-exact-types-v1', 'timing': 'same-timing-boundary'}
    checks = {key: True for key in compare.REQUIRED_CHECKS}
    checks.update(wrong_type_rejected='JayError: data', failed_second_write_rolled_back='JayError: data',
                  duplicate_id={'behavior': 'replaced_existing_row'})
    r = {'scenario': '01_example', 'engine': 'jaydb2', 'status': 'passed', 'checks': checks,
         'samples': [], 'summary': {}, 'create_schema_and_client_ns': 1000,
         'populate_ns': 2000, 'reopen_and_client_prepare_ns': 3000}
    for name in sorted(compare.REQUIRED):
        for i, x in enumerate([120, 100, 110, 90]):
            value = True if name in ('point_update', 'two_row_transaction') else 23
            r['samples'].append({'phase': 'warmup' if i == 0 else 'sample', 'workload': name,
                                 'iteration': i, 'elapsed_ns': x, 'actual': value, 'expected': value, 'checked': True})
        xs = [100, 110, 90]
        r['summary'][name] = {'n': 3, 'median_ns': 100, 'min_ns': 90, 'max_ns': 110,
                               'p95_ns': 110, 'mad_ns': 10}
    return {'status': 'passed', 'finished_utc': '2026-11-06T00:00:01Z', 'settings': settings,
            'results': [r], 'scenario_sha256': {'01_example': 'a'*64},
            'source_sha256': {'server/main.rs': 'b'*64},
            'suite_sha256': {'run.py': 'c'*64, 'jay.py': 'd'*64, 'Access.bend': 'e'*64},
            'git_head': 'baseline-head', 'git_branch': 'bench', 'git_status': '',
            'jay_binary_sha256': 'f'*64, 'versions': {'python': '3.12', 'sqlite': '3.53'},
            'verified_tools': {'bend': '1'*64}, 'toolchain_lock': {'version': '2.0.39'},
            'hardware': {'cpu': 'test', 'affinity': [1], 'logical_cpus': 2}}


def scale_workload(m, workload, factor):
    r = m['results'][0]
    for sample in r['samples']:
        if sample['workload'] == workload:
            sample['elapsed_ns'] = round(sample['elapsed_ns'] * factor)
    xs = [s['elapsed_ns'] for s in r['samples'] if s['workload'] == workload and s['phase'] == 'sample']
    med = statistics.median(xs)
    r['summary'][workload].update(median_ns=med, min_ns=min(xs), max_ns=max(xs), p95_ns=max(xs),
                                  mad_ns=statistics.median(abs(x-med) for x in xs))


class ExactResultTests(unittest.TestCase):
    def test_bool_integer_and_float_are_not_equivalent(self):
        for actual, expected in [(True, 1), (False, 0), (1.0, 1), ([1], [True]),
                                 ({'rows': [{'active': 1}]}, {'rows': [{'active': True}]})]:
            with self.subTest(actual=actual), self.assertRaises(AssertionError):
                check(actual, expected)

    def test_recursive_match_preserves_order_and_dictionary_meaning(self):
        check({'rows': [1, False, {'name': 'é', 'missing': None}]},
              {'rows': [1, False, {'missing': None, 'name': 'é'}]})
        self.assertFalse(model.equal([1, 2], [2, 1]))
        self.assertFalse(model.equal({'extra': None}, {}))


class ComparisonTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.before = fixture()
        self.after = copy.deepcopy(self.before)
        self.paths = [Path(self.tmp.name)/'before.json', Path(self.tmp.name)/'after.json']

    def call(self, **kw):
        for path, obj in zip(self.paths, [self.before, self.after]):
            path.write_text(json.dumps(obj))
        return compare.compare(*self.paths, **kw)

    def test_reports_gains_and_regressions_without_composite_score(self):
        scale_workload(self.after, 'point_read', .5)
        scale_workload(self.after, 'point_update', 1.3)
        r = self.call()
        self.assertEqual(r['status'], 'gate_failed')
        self.assertEqual(len(r['rows']), 7)
        by = {x['workload']: x for x in r['rows']}
        self.assertEqual(by['point_read']['speedup'], 2)
        self.assertEqual(by['point_read']['classification'], 'improvement')
        self.assertEqual(by['point_update']['classification'], 'regression_exceeds_threshold')
        self.assertNotIn('score', r)

    def test_noise_tolerance_does_not_claim_significance(self):
        scale_workload(self.after, 'point_read', 1.03)
        scale_workload(self.after, 'point_update', 1.1)
        r = self.call()
        self.assertEqual(r['status'], 'gate_passed')
        by = {x['workload']: x for x in r['rows']}
        self.assertEqual(by['point_read']['classification'], 'within_tolerance')
        self.assertEqual(by['point_update']['classification'], 'possible_regression')

    def test_setup_changes_are_visible_and_optionally_gated(self):
        self.after['results'][0]['populate_ns'] = 5000
        r = self.call()
        self.assertEqual(r['status'], 'gate_passed')
        self.assertEqual(next(x for x in r['rows'] if x['workload'] == 'populate_ns')['delta_percent'], 150)
        self.assertEqual(self.call(gate_metrics=('latency', 'setup'))['status'], 'gate_failed')

    def test_engine_provenance_changes_are_reported_not_hidden(self):
        self.after['jay_binary_sha256'] = '2'*64
        self.after['source_sha256']['server/main.rs'] = '3'*64
        r = self.call()
        self.assertEqual(r['engine_source_changes'], ['server/main.rs'])
        self.assertNotEqual(r['baseline']['controller_sha256'], r['candidate']['controller_sha256'])

    def test_rejects_changed_fixtures_settings_and_workload_coverage(self):
        cases = []
        x = fixture(); x['scenario_sha256']['01_example'] = '9'*64; cases.append(x)
        x = fixture(); x['settings']['clients'] = 2; cases.append(x)
        x = fixture(); del x['results'][0]['summary']['point_update']; cases.append(x)
        for bad in cases:
            self.after = bad
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                self.call()

    def test_explicit_application_and_environment_changes_are_labelled(self):
        self.after['suite_sha256']['jay.py'] = '4'*64
        with self.assertRaisesRegex(ValueError, 'Measured workload'):
            self.call()
        self.after['hardware']['cpu'] = 'different'
        with self.assertRaisesRegex(ValueError, 'environment differs'):
            self.call(allow_workload_change=True)
        r = self.call(allow_workload_change=True, allow_environment_change=True)
        self.assertEqual(len(r['warnings']), 2)

    def test_unused_query_and_generated_project_sources_do_not_change_legacy_identity(self):
        self.after['suite_sha256']['query/SingleCall.bend'] = '1'*64
        self.after['suite_sha256']['query/backend.py'] = '2'*64
        self.after['suite_sha256']['projects/01_example/jaydb2/Access.bend'] = '3'*64
        self.after['suite_sha256']['projects/01_example/jaydb2/AccessProof.bend'] = '4'*64
        r = self.call()
        self.assertEqual(r['status'], 'gate_passed')
        self.assertEqual(r['warnings'], [])

    def test_changed_used_legacy_bend_source_requires_explicit_profile_flag(self):
        for source in ['Access.bend', 'Batch.bend', 'ReadRow.bend']:
            self.after = fixture()
            self.after['suite_sha256'][source] = '9'*64
            self.before['suite_sha256'].setdefault(source, '8'*64)
            with self.subTest(source=source), self.assertRaisesRegex(ValueError, 'Measured workload'):
                self.call()

    def test_application_profile_metadata_requires_flag_and_is_recorded(self):
        self.after['settings']['profile'] = 'certified-single-call'
        self.after['settings']['profile_metadata'] = {'reads': 'certified', 'query_calls': 1}
        with self.assertRaisesRegex(ValueError, 'profile metadata differs'):
            self.call()
        r = self.call(allow_workload_change=True)
        self.assertEqual(r['profiles']['baseline'], {'profile': 'legacy', 'metadata': {}})
        self.assertEqual(r['profiles']['candidate']['profile'], 'certified-single-call')
        self.assertIn('Application profiles differ:', r['warnings'][0])
        self.assertIn('does not isolate an engine optimization', r['warnings'][0])

    def test_profile_flag_cannot_change_work_or_durability_settings(self):
        for key, value in [('samples', 4), ('warmups', 2), ('durable', False), ('clients', 2),
                           ('jay_threads', 2), ('read_workers', 2), ('result_equality', 'coercing')]:
            self.after = fixture()
            self.after['settings']['profile'] = 'certified-single-call'
            self.after['settings'][key] = value
            with self.subTest(setting=key), self.assertRaises(ValueError):
                self.call(allow_workload_change=True)

    def test_query_profile_does_include_its_used_query_sources(self):
        self.before['settings']['profile'] = self.after['settings']['profile'] = 'certified-single-call'
        self.before['suite_sha256']['query/SingleCall.bend'] = '7'*64
        self.after['suite_sha256']['query/SingleCall.bend'] = '8'*64
        with self.assertRaisesRegex(ValueError, 'Measured workload'):
            self.call()

    def test_explicit_legacy_metadata_matches_historical_missing_profile(self):
        self.after['settings']['profile'] = 'legacy'
        self.after['settings']['profile_metadata'] = {}
        self.assertEqual(self.call()['warnings'], [])

    def test_rejects_fatal_partial_duplicate_and_incorrect_records(self):
        bads = []
        x = fixture(); x['error'] = 'source drift'; bads.append(x)
        x = fixture(); x['status'] = 'running'; bads.append(x)
        x = fixture(); x['results'] = []; bads.append(x)
        x = fixture(); x['results'].append(copy.deepcopy(x['results'][0])); bads.append(x)
        x = fixture(); x['results'][0]['samples'][0]['actual'] = -4; bads.append(x)
        x = fixture(); x['results'][0]['samples'][0]['checked'] = False; bads.append(x)
        x = fixture(); del x['results'][0]['samples'][0]['actual']; del x['results'][0]['samples'][0]['expected']; bads.append(x)
        x = fixture(); x['results'][0]['samples'][0]['actual'] = 1; x['results'][0]['samples'][0]['expected'] = True; bads.append(x)
        x = fixture(); x['results'][0]['summary']['point_read']['median_ns'] = 1; bads.append(x)
        x = fixture(); x['results'][0]['samples'][1]['iteration'] = 2; bads.append(x)
        x = fixture(); x['results'][0]['checks']['full_final_data_after_reopen'] = False; bads.append(x)
        for bad in bads:
            self.after = bad
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                self.call()

    def test_failed_engine_and_semantic_changes_fail_gate(self):
        self.after['status'] = 'failed'
        self.after['results'][0]['status'] = 'failed'
        self.after['results'][0]['error'] = 'init failed'
        r = self.call()
        self.assertEqual(r['status'], 'gate_failed')
        self.assertEqual(len(r['failures']), 1)
        self.after = fixture()
        self.after['results'][0]['checks']['duplicate_id']['behavior'] = 'rejected'
        self.assertEqual(self.call()['status'], 'gate_failed')

    def test_invalid_thresholds_are_rejected(self):
        for noise, failure in [(-1, 5), (20, 15), (0, float('nan')), (float('inf'), 50)]:
            with self.subTest(noise=noise), self.assertRaises(ValueError):
                self.call(noise_percent=noise, fail_regression_percent=failure)

    def test_cli_has_separate_invalid_gate_and_success_exit_codes(self):
        self.call()
        out = Path(self.tmp.name)/'success'
        self.assertEqual(compare.main([str(p) for p in self.paths]+['--output', str(out)]), 0)
        self.assertTrue((out/'comparison.md').exists())
        self.assertEqual(compare.main([str(p) for p in self.paths]+['--output', str(out)]), 2)
        scale_workload(self.after, 'point_read', 2)
        self.call()
        self.assertEqual(compare.main([str(p) for p in self.paths]+['--output', str(out.parent/'fail')]), 1)


if __name__ == '__main__':
    unittest.main()
