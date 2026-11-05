"""Independent oracle evidence; real native performance runs are separate."""
import unittest

import bench


class OracleTests(unittest.TestCase):
    def test_affine_composition_matches_independent_direct_loop(self):
        for n in (0, 1, 2, 31, 32, 4096, 250000, 1000000):
            for seed in (0, 1, 7, 2**31, 2**32-1):
                with self.subTest(n=n, seed=seed):
                    self.assertEqual(bench.reference_compute(n, seed), bench.baseline.compute(n, seed))

    def test_known_answers_and_unsigned_boundaries(self):
        self.assertEqual(bench.reference_compute(0, 2**32-1), 2**32-1)
        self.assertEqual(bench.reference_compute(1, 0), 1013904223)
        self.assertEqual(bench.reference_compute(3, 1), 2165703038)
        # This full-period LCG's predecessor must recover each seed. The
        # one-step check is independent direct arithmetic, not exponentiation.
        for seed in (0, 1, 2**31, 2**32-1):
            previous = bench.reference_compute(2**32-1, seed)
            self.assertEqual((previous*1664525+1013904223) & (2**32-1), seed)
        for n, seed in ((-1, 0), (2**32, 0), (0, -1), (0, 2**32)):
            with self.subTest(n=n, seed=seed):
                with self.assertRaises(ValueError):
                    bench.reference_compute(n, seed)
