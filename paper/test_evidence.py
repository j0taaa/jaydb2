"""Causal controls for the external comparison used by the TCC."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest

MODULE = Path(__file__).with_name('evidence.py')
spec = importlib.util.spec_from_file_location('paper_evidence', MODULE)
evidence = importlib.util.module_from_spec(spec)
spec.loader.exec_module(evidence)


class ComparisonEvidenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        folder = evidence.ROOT / 'paper/evidence'
        cls.data = json.loads((folder / 'results.json').read_text())
        cls.raw = json.loads((folder / 'raw-result.json').read_text())
        cls.audit = json.loads((folder / 'provenance-audit.json').read_text())

    def inputs(self):
        return copy.deepcopy((self.data, self.raw, self.audit))

    def derive(self, data, raw, audit):
        return evidence.comparison_statistics(data, raw, audit,
                                             evidence.COMPARISON_DIGESTS['raw-result.json'])

    def mutate_records(self, operation):
        data, raw, audit = self.inputs()
        # Change both copies so provenance-copy equality cannot be the reason
        # the intended semantic guard rejects the corrupted measurement.
        operation(data['results'])
        operation(raw['results'])
        return data, raw, audit

    def test_retained_point_operation_values(self):
        result = self.derive(*self.inputs())
        expected = {
            ('point_read', 'jaydb2'): 127.333497,
            ('point_read', 'postgresql'): 0.0862605,
            ('point_read', 'sqlite'): 0.0125605,
            ('point_update', 'jaydb2'): 117.7148525,
            ('point_update', 'postgresql'): 3.5233465,
            ('point_update', 'sqlite'): 5.750861,
        }
        self.assertEqual(set(result), set(expected))
        for key, number in expected.items():
            self.assertAlmostEqual(result[key], number, places=8)

    def test_duplicate_engine_record_is_not_an_extra_success(self):
        data = self.mutate_records(lambda rows: rows.__setitem__(-1, copy.deepcopy(rows[0])))
        with self.assertRaisesRegex(ValueError, 'engine/scenario records'):
            self.derive(*data)

    def test_duplicate_iteration_cannot_replace_a_measured_sample(self):
        def corrupt(rows):
            samples = [s for s in rows[0]['samples'] if s['workload'] == 'point_read' and s['phase'] == 'sample']
            samples[1]['iteration'] = samples[0]['iteration']
        with self.assertRaisesRegex(ValueError, 'point-operation samples'):
            self.derive(*self.mutate_records(corrupt))

    def test_checked_flag_does_not_override_a_wrong_result_or_type(self):
        def corrupt(rows):
            sample = next(s for s in rows[0]['samples'] if s['workload'] == 'point_update')
            self.assertIs(sample['actual'], True)
            sample['actual'] = 1
        with self.assertRaisesRegex(ValueError, 'output disagrees'):
            self.derive(*self.mutate_records(corrupt))

    def test_retained_summary_must_match_measured_latencies(self):
        with self.assertRaisesRegex(ValueError, 'summary disagrees'):
            self.derive(*self.mutate_records(lambda rows: rows[0]['summary']['point_read'].__setitem__('median_ns', 1)))

    def test_audit_cannot_relabel_unrelated_raw_measurements(self):
        data, raw, audit = self.inputs()
        audit['raw_result_sha256'] = '0' * 64
        data['provenance_audit'] = audit
        with self.assertRaisesRegex(ValueError, 'does not bind the raw result'):
            self.derive(data, raw, audit)


if __name__ == '__main__':
    unittest.main(verbosity=2)
