"""Causal S1/S2 fixtures through Database.request and prepared completion.

Injected Python/known nonconsuming errors and C epochs are explicit fixtures.
Actual output release/unload is observed; none is a MedicaoReal observation.
"""
import ctypes as C
import gc
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
import weakref
from unittest.mock import patch

from tools.native import accounted
from tools.service import controller, loading
from tools.service.abi import Module
from tools.service.build_commit import build
from tests.service import test_completion, test_lifecycle_consumers
from tests.service.runtime_profile import fixture_lifecycle

ROOT = Path(__file__).resolve().parents[2]


class CompletionV5Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.runtime = fixture_lifecycle()
        cls.loading = loading.Runtime.current()
        cls.temp = tempfile.TemporaryDirectory(prefix='jaydb-completion-v5-')
        cls.folder = Path(cls.temp.name)
        cls.library = cls.folder/'commit.so'
        build(cls.library, test_fixture=ROOT/'tests/service/commit_fixture.c')
        cls.module_path = cls.folder/'execute.so'
        subprocess.run(['/usr/bin/clang-19', '-shared', '-fPIC', '-O2', '-Wall', '-Wextra',
                        '-Werror', str(ROOT/'tests/service/completion_v5_fixture.c'),
                        '-o', str(cls.module_path)], check=True)
        cls.module_path.with_suffix('.so.json').write_text(json.dumps({
            'moduleSha256': hashlib.sha256(cls.module_path.read_bytes()).hexdigest(),
            'sourceSha256': 'a'*64, 'imageBytes': 4096, 'ownedOutputV3': True,
            'demandStableHeapV3': True, 'durationBitsV3': 128, 'absoluteSetupDeadlineV3': True,
            'automaticTermStackV3': True, 'automaticNativeStackV3': True,
            'automaticNativeStackModeV3': 'linux-main-growdown', 'nativeStackClashProtection': True}))
        accounted.install_accounted(Module, incomplete_type=controller.IncompleteIntegration)

    @classmethod
    def tearDownClass(cls):
        assert not cls.runtime.live_processes
        assert not cls.runtime.live_leases
        cls.temp.cleanup()

    def request_fixture(self, *, epoch=10**30, stage=2, flags=3, run_error=0):
        db, root, counter, completion, *_ = test_completion.CompletionTests.setup_request(self)
        db.loading_runtime, db.lifecycle_runtime = self.loading, self.runtime
        db.bind_request_completion(completion, instrument_deadline_ns=10**30)
        captured = []
        stats = test_lifecycle_consumers.Stats()
        def compile_request(*args, **options):
            # The V4 causal run predates the explicit scope parameter.
            extra = {'library_scope': options['library_scope']} if 'library_scope' in options else {}
            m = Module(self.module_path, loading_runtime=self.loading,
                       lifecycle_runtime=self.runtime, **extra)
            captured.append(m)
            self.addCleanup(m.close)
            f = m.library.lifecycle_fixture_configure
            f.argtypes = [C.POINTER(type(stats)), C.c_char_p, C.c_uint32, C.c_uint32,
                          C.c_int, C.c_int, C.c_uint]
            f(C.byref(stats), None, 0, run_error, 0, 0, 0)
            f = m.library.completion_v5_epoch
            f.argtypes = [C.c_uint64, C.c_uint64, C.c_uint32, C.c_uint64]
            f(epoch & (2**64-1), epoch >> 64, stage, flags)
            return m, db.limits
        return db, root, completion, compile_request, captured, stats

    def test_S1_preentry_dso_close_blocks_completion(self):
        db, root, completion, compile_request, modules, stats = self.request_fixture()
        published = root.native.published
        with patch.object(controller, 'build', side_effect=compile_request), \
                patch.object(self.loading, '_close', side_effect=MemoryError('fixture before C close')):
            with self.assertRaises(controller.IncompleteIntegration):
                db.request(b'body')
        self.assertIsNone(root.native.completed)
        self.assertIsNone(completion.prepared)
        self.assertEqual(root.native.published, published)
        self.assertEqual((stats.releases, stats.destructors), (1, 0))
        self.assertFalse(self.runtime.live_leases)
        self.assertIn(modules[0]._library_owner, self.loading.live_owners)

    def test_S2_persistent_receipt_failure_preserves_raw_epoch(self):
        epoch = 10**30
        db, root, completion, compile_request, modules, stats = self.request_fixture(epoch=epoch)
        finish = completion.finish
        def check_epoch(*args, **options):
            self.assertEqual(options['deadline_ns'], epoch)
            return finish(*args, **options)
        with patch.object(controller, 'build', side_effect=compile_request), \
                patch.object(accounted.Receipt, 'read', side_effect=MemoryError('fixture diagnostic wrapper')), \
                patch.object(completion, 'finish', side_effect=check_epoch):
            db.request(b'body')
        self.assertIsNone(modules[0].last_accounted_receipt)
        self.assertEqual((stats.releases, stats.destructors, stats.live_at_destructor), (1, 1, 0))

    def assert_blocked(self, root, completion, published):
        self.assertIsNone(root.native.completed)
        self.assertIsNone(completion.prepared)
        self.assertEqual(root.native.published, published)

    def close_database(self, db):
        # Host-only decode/auth fixtures have no close method or native owner.
        db.modules = {}
        db.close()

    def test_known_nonconsuming_close_error_is_retained_for_database_retry(self):
        db, root, completion, compile_request, modules, stats = self.request_fixture()
        published = root.native.published
        def nonconsuming(opened, closed):
            # Declared fixture: C was entered and returned DL_ERROR, no dlclose.
            r = C.cast(closed, C.POINTER(loading._CloseReceipt)).contents
            r.entered, r.outcome = 1, (loading.DL_ERROR << 32) | 1
            return loading.DL_ERROR
        with patch.object(controller, 'build', side_effect=compile_request), \
                patch.object(self.loading, '_close', nonconsuming):
            with self.assertRaises(controller.IncompleteIntegration):db.request(b'body')
            self.assert_blocked(root, completion, published)
            owner, = db._request_libraries.live_owners
            self.assertFalse(owner.closed)
            db.modules = {}
            with self.assertRaises(loading.CloseError):db.close()
            self.assertIn(owner, db._request_libraries.live_owners)
        self.close_database(db)
        self.assertTrue(owner.closed)
        self.assertFalse(db._request_libraries.live_owners)
        self.assertEqual((stats.releases, stats.destructors, stats.live_at_destructor), (1, 1, 0))
        with patch.object(self.loading, '_close', side_effect=AssertionError('double dlclose')):
            db.close()

    def test_real_close_then_python_failure_does_not_block_or_repeat_consumption(self):
        db, root, completion, compile_request, modules, stats = self.request_fixture()
        close = self.loading._close
        calls = []
        def interrupted(*args):
            calls.append(close(*args))
            raise MemoryError('fixture after C dlclose success')
        with patch.object(controller, 'build', side_effect=compile_request), \
                patch.object(self.loading, '_close', interrupted):
            self.assertEqual(db.request(b'body'), controller.error_frame('falha'))
        self.assertTrue(completion.completed)
        self.assertFalse(db._request_libraries.live_owners)
        self.assertEqual(len(calls), 1)
        self.assertEqual((stats.releases, stats.destructors, stats.live_at_destructor), (1, 1, 0))
        with patch.object(self.loading, '_close', side_effect=AssertionError('double dlclose')):
            modules[0].close()

    def test_failure_before_acquisition_can_complete_without_pending_owner(self):
        db, root, completion, compile_request, modules, stats = self.request_fixture()
        with patch.object(controller, 'build', side_effect=compile_request), \
                patch.object(self.loading, '_open', side_effect=MemoryError('fixture before dlopen')):
            self.assertEqual(db.request(b'body'), controller.error_frame('falha'))
        self.assertTrue(completion.completed)
        self.assertFalse(db._request_libraries.live_owners)
        self.assertFalse(modules)
        self.assertEqual(stats.runs, 0)

    def test_open_return_assignment_failure_remains_in_database_scope(self):
        db, root, completion, compile_request, modules, stats = self.request_fixture()
        published = root.native.published
        opened = loading.LibraryOwner.open
        def interrupted(*args, **options):
            opened(*args, **options)
            raise MemoryError('fixture before Module owner assignment')
        with patch.object(controller, 'build', side_effect=compile_request), \
                patch.object(loading.LibraryOwner, 'open', side_effect=interrupted), \
                patch.object(self.loading, '_close', side_effect=MemoryError('fixture cleanup pending')):
            with self.assertRaises(controller.IncompleteIntegration):db.request(b'body')
        self.assert_blocked(root, completion, published)
        owner, = db._request_libraries.live_owners
        self.assertFalse(modules)  # constructor never returned, no local module to recover
        self.assertIsNotNone(owner.library)
        self.close_database(db)
        self.assertTrue(owner.closed)

    def test_library_property_failure_during_constructor_is_guarded(self):
        db, root, completion, compile_request, modules, stats = self.request_fixture()
        published = root.native.published
        with patch.object(controller, 'build', side_effect=compile_request), \
                patch.object(Module, 'library', property(lambda _: (_ for _ in ()).throw(
                    MemoryError('fixture Module.library')))), \
                patch.object(self.loading, '_close', side_effect=MemoryError('fixture cleanup pending')):
            with self.assertRaises(controller.IncompleteIntegration):db.request(b'body')
        self.assert_blocked(root, completion, published)
        owner, = db._request_libraries.live_owners
        self.assertFalse(modules)
        self.close_database(db)
        self.assertTrue(owner.closed)

    def test_exception_inside_dlopen_return_is_scoped_before_wrapper_setup(self):
        db, root, completion, compile_request, modules, stats = self.request_fixture()
        published = root.native.published
        opened = self.loading._open
        def interrupted(*args):
            opened(*args)
            raise MemoryError('fixture after C dlopen before wrapper')
        with patch.object(controller, 'build', side_effect=compile_request), \
                patch.object(self.loading, '_open', interrupted), \
                patch.object(self.loading, '_close', side_effect=MemoryError('fixture cleanup pending')):
            with self.assertRaises(controller.IncompleteIntegration):db.request(b'body')
        self.assert_blocked(root, completion, published)
        owner, = db._request_libraries.live_owners
        self.assertIsNone(owner._library)
        self.close_database(db)
        self.assertTrue(owner.closed)

    def test_persistent_request_registry_failure_is_outside_mapper(self):
        db, root, completion, compile_request, modules, stats = self.request_fixture()
        published = root.native.published
        read = loading.LibraryScope.live_owners.fget
        def registry(scope):
            owners = read(scope)
            if owners:raise MemoryError('fixture persistent request registry')
            return owners
        with patch.object(controller, 'build', side_effect=compile_request), \
                patch.object(self.loading, '_close', side_effect=MemoryError('fixture cleanup pending')), \
                patch.object(loading.LibraryScope, 'live_owners', property(registry)):
            with self.assertRaisesRegex(MemoryError, 'persistent request registry'):db.request(b'body')
        self.assert_blocked(root, completion, published)
        self.close_database(db)
        self.assertEqual((stats.releases, stats.destructors), (1, 1))

    def test_pending_library_blocks_next_request_before_proposal(self):
        db, root, completion, compile_request, modules, stats = self.request_fixture()
        with patch.object(controller, 'build', side_effect=compile_request), \
                patch.object(self.loading, '_close', side_effect=MemoryError('fixture pending')):
            with self.assertRaises(controller.IncompleteIntegration):db.request(b'body')
        with patch.object(db, '_propose_request', side_effect=AssertionError('new proposal')):
            with self.assertRaises(controller.IncompleteIntegration):db.request(b'next')
        self.close_database(db)

    def test_baseline_with_same_path_is_explicitly_outside_request_scope(self):
        baseline = loading.LibraryOwner.open(self.loading, self.module_path)
        self.addCleanup(baseline.close)
        db, root, completion, compile_request, modules, stats = self.request_fixture()
        with patch.object(controller, 'build', side_effect=compile_request):
            self.assertEqual(db.request(b'body'), controller.error_frame('falha'))
        self.assertTrue(completion.completed)
        self.assertFalse(db._request_libraries.live_owners)
        self.assertIn(baseline, self.loading.live_owners)
        self.assertEqual(stats.destructors, 0)
        baseline.close()
        self.assertEqual((stats.destructors, stats.live_at_destructor), (1, 0))

    def test_raw_epoch_unreadable_blocks_completion_after_release_and_unload(self):
        db, root, completion, compile_request, modules, stats = self.request_fixture()
        published = root.native.published
        with patch.object(controller, 'build', side_effect=compile_request), \
                patch.object(accounted.EpochAuthority, 'deadline_ns',
                             side_effect=MemoryError('fixture raw scalar unavailable')):
            with self.assertRaisesRegex(MemoryError, 'raw scalar unavailable'):db.request(b'body')
        self.assert_blocked(root, completion, published)
        self.assertFalse(db._request_libraries.live_owners)
        self.assertEqual((stats.releases, stats.destructors, stats.live_at_destructor), (1, 1, 0))

    def test_transient_raw_read_failure_is_recovered_outside_mapper(self):
        epoch = 10**30
        db, root, completion, compile_request, modules, stats = self.request_fixture(epoch=epoch)
        read = accounted.EpochAuthority.deadline_ns
        reads = []
        def transient(authority):
            reads.append(True)
            if len(reads) == 1:raise MemoryError('fixture first raw read')
            return read(authority)
        finish = completion.finish
        def checked(*args, **options):
            self.assertEqual(options['deadline_ns'], epoch)
            return finish(*args, **options)
        with patch.object(controller, 'build', side_effect=compile_request), \
                patch.object(accounted.EpochAuthority, 'deadline_ns', transient), \
                patch.object(completion, 'finish', side_effect=checked):
            db.request(b'body')
        self.assertEqual(len(reads), 2)
        self.assertTrue(completion.completed)
        self.assertEqual((stats.releases, stats.destructors), (1, 1))

    def test_receipt_failure_preserves_execution_and_preparation_time_equality(self):
        for stage in (1, 2):
            for epoch in (99, 100, 101):
                with self.subTest(stage=stage, epoch=epoch):
                    db, root, completion, compile_request, modules, stats = self.request_fixture(
                        epoch=epoch, stage=stage)
                    with patch.object(controller, 'build', side_effect=compile_request), \
                            patch.object(accounted.Receipt, 'read', side_effect=MemoryError('fixture wrapper')):
                        response = db.request(b'body')
                    self.assertEqual(response, controller.error_frame('limite' if epoch <= 100 else 'falha'))
                    self.assertEqual(db._request_native_deadline, epoch)
                    self.assertEqual((stats.releases, stats.destructors), (1, 1))

    def test_native_failure_retains_original_epoch_without_output(self):
        for stage in (1, 2):
            with self.subTest(stage=stage):
                db, root, completion, compile_request, modules, stats = self.request_fixture(
                    epoch=100, stage=stage, run_error=3)
                with patch.object(controller, 'build', side_effect=compile_request):
                    self.assertEqual(db.request(b'body'), controller.error_frame('limite'))
                self.assertEqual(db.last_failure, {'code':'NATIVE','status':3,'runtime_code':0,'stage':stage})
                self.assertEqual(db._request_native_deadline, 100)
                self.assertEqual((stats.allocations, stats.releases, stats.destructors), (0, 0, 1))

    def test_raw_epoch_survives_exception_after_native_invoke_return(self):
        db, root, completion, compile_request, modules, stats = self.request_fixture(epoch=100)
        invoke = self.runtime._invoke
        def interrupted(*args):
            invoke(*args)
            raise MemoryError('fixture after C invoke')
        with patch.object(controller, 'build', side_effect=compile_request), \
                patch.object(self.runtime, '_invoke', interrupted), \
                patch.object(accounted.Receipt, 'read', side_effect=MemoryError('fixture wrapper')):
            self.assertEqual(db.request(b'body'), controller.error_frame('limite'))
        self.assertEqual(db._request_native_deadline, 100)
        self.assertEqual((stats.releases, stats.destructors, stats.live_at_destructor), (1, 1, 0))

    def test_missing_raw_timing_never_reuses_verification_epoch(self):
        db, root, completion, compile_request, modules, stats = self.request_fixture(flags=0)
        published = root.native.published
        with patch.object(controller, 'build', side_effect=compile_request):
            with self.assertRaises(controller.IncompleteIntegration):db.request(b'body')
        self.assert_blocked(root, completion, published)
        self.assertEqual((stats.releases, stats.destructors), (1, 1))

    def test_native_failure_cause_survives_later_diagnostic_allocation_failure(self):
        db, root, completion, compile_request, modules, stats = self.request_fixture(
            epoch=10**30, stage=1, run_error=3)
        read = accounted.Receipt.read
        calls = []
        def diagnostic(out):
            calls.append(True)
            if len(calls) > 1:raise MemoryError('fixture later diagnostic')
            return read(out)
        with patch.object(controller, 'build', side_effect=compile_request), \
                patch.object(accounted.Receipt, 'read', side_effect=diagnostic):
            self.assertEqual(db.request(b'body'), controller.error_frame('limite'))
        self.assertEqual(db.last_failure, {'code':'NATIVE','status':3,'runtime_code':0,'stage':1})
        self.assertEqual(db._request_native_deadline, 10**30)
        self.assertEqual((stats.allocations, stats.releases, stats.destructors), (0, 0, 1))

    def test_primary_host_failure_survives_exception_after_consumed_release(self):
        db, root, completion, compile_request, modules, stats = self.request_fixture(epoch=100)
        release = self.runtime._release
        def interrupted(*args):
            release(*args)
            raise RuntimeError('fixture after consumed release')
        with patch.object(controller, 'build', side_effect=compile_request), \
                patch.object(accounted.Receipt, 'read', side_effect=MemoryError('fixture primary diagnostic')), \
                patch.object(self.runtime, '_release', interrupted):
            self.assertEqual(db.request(b'body'), controller.error_frame('limite'))
        self.assertEqual(db.last_failure['code'], 'MemoryError')
        self.assertEqual(db.last_failure['message'], 'fixture primary diagnostic')
        self.assertEqual(db._request_native_deadline, 100)
        self.assertEqual((stats.release_calls, stats.releases, stats.destructors), (1, 1, 1))

    def test_native_failure_cause_survives_exception_after_consumed_dso_close(self):
        db, root, completion, compile_request, modules, stats = self.request_fixture(
            epoch=10**30, stage=1, run_error=3)
        close = self.loading._close
        def interrupted(*args):
            close(*args)
            raise MemoryError('fixture after consumed dlclose')
        with patch.object(controller, 'build', side_effect=compile_request), \
                patch.object(self.loading, '_close', interrupted):
            self.assertEqual(db.request(b'body'), controller.error_frame('limite'))
        self.assertEqual(db.last_failure, {'code':'NATIVE','status':3,'runtime_code':0,'stage':1})
        self.assertEqual(db._request_native_deadline, 10**30)
        self.assertEqual((stats.allocations, stats.releases, stats.destructors), (0, 0, 1))

    def test_no_native_entry_keeps_setup_epoch_after_invoke_preentry_failure(self):
        db, root, completion, compile_request, modules, stats = self.request_fixture(epoch=100)
        seen = []
        def stage(*args, **options):
            seen.append(options['deadline'])
            return compile_request(*args, **options)
        finish = completion.finish
        def check_setup(*args, **options):
            self.assertEqual(options['deadline_ns'], seen[0])
            return finish(*args, **options)
        with patch.object(controller, 'build', side_effect=stage), \
                patch.object(self.runtime, '_invoke', side_effect=MemoryError('fixture before invoke C')), \
                patch.object(completion, 'finish', side_effect=check_setup):
            self.assertEqual(db.request(b'body'), controller.error_frame('falha'))
        self.assertEqual((stats.runs, stats.allocations, stats.destructors), (0, 0, 1))
        self.assertIsNone(db._request_native_deadline)

    def test_database_close_drops_retained_epoch_module_and_request_buffers(self):
        db, root, completion, compile_request, modules, stats = self.request_fixture()
        with patch.object(controller, 'build', side_effect=compile_request):
            db.request(b'body')
        module = modules.pop()
        reference = weakref.ref(module)
        # Remove this test's bound-method cleanup reference; C is already closed.
        self._cleanups = [entry for entry in self._cleanups
                          if getattr(entry[0], '__self__', None) is not module]
        del module
        self.close_database(db)
        gc.collect()
        self.assertIsNone(reference())
        self.assertIsNone(db._request_epoch_module)
        self.assertEqual((stats.releases, stats.destructors), (1, 1))


if __name__ == '__main__':
    unittest.main(verbosity=2)
