#!/usr/bin/env python3
"""Real ctypes return, lease cleanup and memory-boundary regressions.

The test fixture emitter checks primary typing only. It is confined to tests;
production still admits the same Book with both checkers before compilation.
"""
from pathlib import Path
import os
import re
import resource
import signal
import subprocess
import sys
import tarfile
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.service.abi import Module
from tools.service.build_loading import build as build_loading
from tools.service.loading import Runtime as LoadingRuntime


class NativeAbiBoundary(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix='jaydb-service-native-abi-')
        cls.addClassCleanup(cls.temp.cleanup)
        root = Path(cls.temp.name)
        checkpoint = Path(os.environ.get('JAYDB_TEST_NATIVE_CHECKPOINT',ROOT / 'tests/native/checkpoints/v3_owned.tar.gz'))
        with tarfile.open(checkpoint) as archive:
            archive.extractall(root, filter='data')
        fixtures = root / 'tests/native/fixtures'
        fixtures.mkdir(parents=True, exist_ok=True)
        for relative in ('tests/native/emit_fixture.mjs', 'tests/native/fixtures/echo.bend'):
            (root / relative).write_bytes((ROOT / relative).read_bytes())
        source = root / 'echo.c'
        subprocess.run(['node', str(root / 'tests/native/emit_fixture.mjs'),
            str(ROOT / '.tools/bend-source-2.0.39/bend2'), str(fixtures / 'echo.bend'), str(source)],
            capture_output=True, check=True, timeout=30)
        c = source.read_text()
        read = re.search(r'^#define (CID_\w*native_effects_read) \d+$', c, re.M)[1]
        write = re.search(r'^#define (CID_\w*native_effects_write) \d+$', c, re.M)[1]
        output = root / 'echo.so'
        subprocess.run([sys.executable, str(root / 'tools/native/build.py'), str(source), str(output),
            '--input-cid', read, '--output-cid', write], capture_output=True, check=True, timeout=120)
        loader=root/'loading.so'
        runtime=LoadingRuntime.load(loader,manifest=build_loading(loader))
        from tests.service.runtime_profile import fixture_lifecycle
        lifecycle=fixture_lifecycle(runtime)
        cls.module = Module(output,loading_runtime=runtime,lifecycle_runtime=lifecycle)
        cls.addClassCleanup(cls.module.close)
        if cls.module.automatic_native:
            from tools.service.entry import prepare_entry
            previous = resource.getrlimit(resource.RLIMIT_STACK)
            prepare_entry()
            cls.addClassCleanup(resource.setrlimit,resource.RLIMIT_STACK,previous)

    def call(self, data=b'x', memory=64 * 1024**2):
        return self.module.run(data, capacity=max(1, len(data)), memory=memory, timeout_ns=10**10)

    def test_non_page_aligned_memory_is_a_valid_budget(self):
        for memory in (64 * 1024**2, 64 * 1024**2 + 16, 64 * 1024**2 + 65536, 4 * 1024**2):
            with self.subTest(memory=memory):
                self.assertEqual(self.call(memory=memory), b'x')

    def test_huge_logical_limits_do_not_allocate_the_ceiling(self):
        self.assertEqual(self.module.run(b'actual', capacity=10**5000, memory=10**5000,
            timeout_ns=10**5000), b'actual')

    def test_current_checkpoint_uses_main_stack_and_original_absolute_epoch(self):
        if not self.module.automatic_native:
            self.skipTest('historical V3 checkpoint predates the main-stack interface')
        from tools.service.abi import NativeFailure
        self.assertTrue(self.module.automatic_terms)
        self.assertTrue(self.module.absolute_setup)
        with self.assertRaises(NativeFailure) as failure:
            self.module.run(b'candidate',capacity=9,memory=4*1024**2,
                timeout_ns=10**9,setup_deadline_ns=0)
        self.assertEqual((failure.exception.status,failure.exception.stage),(3,0))
        self.assertEqual(self.call(b'after deadline'),b'after deadline')

    def test_exception_delivered_at_ctypes_return_releases_native_lease(self):
        class AlarmRaised(RuntimeError):
            pass

        def alarm(signum, frame):
            raise AlarmRaised('signal delivered at ctypes return')

        previous = signal.signal(signal.SIGALRM, alarm)
        try:
            signal.setitimer(signal.ITIMER_REAL, 0.002)
            try:
                with self.assertRaises(AlarmRaised):
                    self.call(b'x' * 100000)
            finally:
                signal.setitimer(signal.ITIMER_REAL, 0)
            # A retained lease would cause BUSY=2 here.
            self.assertEqual(self.call(), b'x')
        finally:
            signal.setitimer(signal.ITIMER_REAL, 0)
            signal.signal(signal.SIGALRM, previous)


if __name__ == '__main__':
    unittest.main(verbosity=2)
