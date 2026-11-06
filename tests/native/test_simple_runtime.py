"""Compile unmodified official C; exercise the application effects/process bridge."""
from __future__ import annotations
from pathlib import Path
import os
import resource
import struct
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
BEND = ROOT/'.tools/bend-source-2.0.39/bend2'


class RuntimeTests(unittest.TestCase):
    threads = 1

    @classmethod
    def setUpClass(cls):
        soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
        if hard != resource.RLIM_INFINITY:
            raise RuntimeError('The native test profile requires an unlimited hard stack')
        resource.setrlimit(resource.RLIMIT_STACK, (resource.RLIM_INFINITY, hard))
        cls.temporary = tempfile.TemporaryDirectory(prefix='jaydb-runtime-test-')
        cls.directory = Path(cls.temporary.name)
        cls.paths = {}

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    @classmethod
    def compile(cls, name):
        if name in cls.paths:
            return cls.paths[name]
        source, output = cls.directory/(name+'.c'), cls.directory/(name+'.program')
        run = subprocess.run(['node', '--stack_size=65536', str(ROOT/'tests/native/emit_fixture.mjs'),
            str(BEND), str(ROOT/'tests/native/fixtures'/(name+'.bend')), str(source)],
            capture_output=True, text=True, timeout=60)
        if run.returncode:
            raise AssertionError(run.stdout+run.stderr)
        original = source.read_bytes()
        subprocess.run(['/usr/bin/clang-19', '-std=gnu11', '-O2', '-w', '--no-default-config',
            str(source), '-o', str(output), '-lm', '-pthread'], check=True, capture_output=True)
        if source.read_bytes() != original:
            raise AssertionError('The official emitted C was modified')
        cls.paths[name] = output
        return output

    def execute(self, name, incoming):
        return subprocess.run([str(self.compile(name)), '+RTS', '--threads', str(self.threads), '--gpu', 'off', '-RTS'],
            input=incoming, capture_output=True, timeout=30, check=True).stdout

    def test_binary_effects_and_fresh_processes(self):
        for data in (bytes(range(256)), b'', b'\0\xffagain', b'x'*131072):
            self.assertEqual(self.execute('echo', data), data)

    def test_official_representations_and_explicit_native_limits(self):
        self.assertEqual(self.execute('representation', b'\3\x11'), str(2**20+1+17).encode())
        self.assertEqual(self.execute('representation', b'\2' + b'1.25'), b'\1'+struct.pack('<f', 1.25))
        self.assertEqual(self.execute('representation', b'\2' + b'1\0garbage'), b'\0')

    def test_official_failure_does_not_affect_another_process(self):
        # These formerly depended on a modified compiler/runtime. Preserve
        # them as explicit official failures, never claim the features work.
        for incoming, diagnostic in ((b'\0\x11', b'a Nat past the largest immediate 2^48-1'),
                                     (b'\1', b'runtime fail-stop')):
            with self.subTest(incoming=incoming), self.assertRaises(subprocess.CalledProcessError) as failure:
                self.execute('representation', incoming)
            self.assertIn(diagnostic, failure.exception.stderr)
        self.assertEqual(self.execute('representation', b'\4'), b'\x08')

    def test_native_loop_prepare_and_continue(self):
        self.assertEqual(self.execute('loop', b'\1\0\2'), b'\2\1')

    def test_checked_length_conversion_and_tail_overflow(self):
        # These include the benchmark's actual ceilings and the full U32
        # endpoint. A linear predecessor conversion at that endpoint cannot
        # finish within the ordinary native-test timeout.
        for value in (0, 1, 255, 65536, 262144, 8388608, 2**32-1):
            with self.subTest(value=value):
                packet = b'\0' + value.to_bytes(4, 'big')
                self.assertEqual(self.execute('fast_bytes', packet),
                                 b'\1' + value.to_bytes(8, 'big'))
        # Exercise the proved tail fallback independently of its fast guard.
        for value in (0, 1, 31, 65536):
            self.assertEqual(self.execute('fast_bytes', b'\1'+value.to_bytes(4, 'big')),
                             b'\1'+value.to_bytes(8, 'big'))
        self.assertEqual(self.execute('fast_bytes', b'\2\0'), b'\1'+(2**64-2).to_bytes(8, 'big'))
        self.assertEqual(self.execute('fast_bytes', b'\2\1'), b'\1'+(2**64-1).to_bytes(8, 'big'))
        self.assertEqual(self.execute('fast_bytes', b'\2\2'), b'\0')
        self.assertEqual(self.execute('fast_bytes', b'\2\3'), b'\0')

    def test_parallel_reduction_matches_independent_reference(self):
        def leaf(value):
            for _ in range(64):
                value = ((value ^ (value >> 16)) * 1664525 + 1013904223) & 0xffffffff
            return value

        depth = 14
        expected = sum(leaf(seed) for seed in range(1 << depth)) & 0xffffffff
        self.assertEqual(self.execute('parallel', bytes([depth])), expected.to_bytes(4, 'little'))


class ParallelRuntimeTests(RuntimeTests):
    threads = min(128, len(os.sched_getaffinity(0)))


if __name__ == '__main__':
    unittest.main(verbosity=2)
