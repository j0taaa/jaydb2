"""Lightweight runner boundaries; real admission/native coverage is run.sh --smoke."""
import contextlib
import io
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
spec = importlib.util.spec_from_file_location('bench', HERE/'bench.py')
bench = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bench)
spec = importlib.util.spec_from_file_location('wire', ROOT/'tools/client.py')
wire = importlib.util.module_from_spec(spec)
spec.loader.exec_module(wire)


class BenchmarkTests(unittest.TestCase):
    def test_statistics_preserve_variability_and_exclude_warmups(self):
        def record(t, phase='sample'):
            return dict(rows=8, mode='ordinary', workload='read', elapsed_ns=t, phase=phase)
        result, = bench.summary([record(2), record(4), record(12), record(100, 'warmup')])
        self.assertEqual(result['n'], 3)
        self.assertEqual(result['median_ns'], 4)
        self.assertEqual(result['median_absolute_deviation_ns'], 2)
        self.assertEqual((result['min_ns'], result['max_ns']), (2, 12))
        self.assertGreater(result['coefficient_of_variation'], 0)
        one, = bench.summary([record(2)])
        self.assertIsNone(one['sample_stdev_ns'])

    def test_smoke_and_default_have_repeats_and_distinct_meaningful_sizes(self):
        smoke = bench.parse_args(['--smoke'])
        normal = bench.parse_args([])
        self.assertGreaterEqual(smoke.samples, 2)
        self.assertGreater(normal.compute_iterations, smoke.compute_iterations)
        self.assertEqual(smoke.rows, [8, 64])
        sizes = [len(wire.encode(bench.seed_state(n))) for n in normal.rows]
        self.assertGreater(sizes[-1], sizes[0]*20)
        self.assertLess(sizes[-1], 65536)
        self.assertEqual(sizes, sorted(set(sizes)))

    def test_bad_measurement_settings_fail_before_starting_a_server(self):
        for args in (['--samples', '1'], ['--warmups', '-1'], ['--threads', '0'],
                     ['--threads', '129'], ['--rows', '7'], ['--rows', '257'],
                     ['--rows', '8', '8'], ['--compute-iterations', '4294967295']):
            with self.subTest(args=args), contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                bench.parse_args(args)

    def test_compute_reference_known_answers_and_runtime_input_changes(self):
        self.assertEqual(bench.compute(0, 7), 7)
        self.assertEqual(bench.compute(1, 0), 1013904223)
        self.assertEqual(bench.compute(3, 1), 2165703038)
        self.assertNotEqual(bench.compute(4096, 1), bench.compute(4097, 1))
        self.assertNotEqual(bench.compute(4096, 1), bench.compute(4096, 2))

    def test_mismatch_is_recorded_and_fails_instead_of_reporting_a_timing(self):
        # A deliberately wrong wire response exercises the external harness,
        # not a replacement for any real JayDB admission or execution test.
        with tempfile.TemporaryDirectory() as temp:
            folder = Path(temp)
            fake = folder/'fake.py'
            response = wire.frame({'status': 'success', 'value': 999})
            fake.write_text(f'import sys\nsys.stdin.buffer.read(1)\nsys.stdout.buffer.write({response!r})\nsys.stdout.buffer.flush()\n')
            records = []
            session = object.__new__(bench.Session)
            session.client, session.records, session.rows = wire, records, 8
            session.errors = (folder/'server.log').open('wb')
            session.process = subprocess.Popen([sys.executable, str(fake)], stdin=subprocess.PIPE,
                                               stdout=subprocess.PIPE, start_new_session=True)
            try:
                with self.assertRaises(AssertionError):
                    session.exchange(b'x', phase='sample', mode='ordinary', workload='read',
                                     expected={'status': 'success', 'value': 1})
                self.assertFalse(records[0]['checked'])
                self.assertEqual(bench.summary(records), [])
                saved = json.loads((folder/'requests.jsonl').read_text())
                self.assertEqual(saved['actual']['value'], 999)
            finally:
                session.close(False)

    def test_output_cannot_escape_target(self):
        with tempfile.TemporaryDirectory() as temp, self.assertRaises(ValueError):
            bench.main(['--root', temp, '--output', str(Path(temp).parent/'outside-benchmark')])


if __name__ == '__main__':
    unittest.main()
