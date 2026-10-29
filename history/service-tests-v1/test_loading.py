"""Causal receipt/ownership tests. No invalid handle is closed in this process.

Targets are ordinary unloadable DSOs. Destructor counters/logs observe real
dlclose effects. Explicit monkeypatches and the wrapped libdl failure are labelled
fixtures; none of these is a witness of physical memory exhaustion or coverage.
Runtime identity/poison tests use fresh subprocesses because installation is
intentionally a single fixed operation per process.
"""
from __future__ import annotations

import ctypes as C
import dataclasses
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from unittest import mock
import weakref

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.service import build_loading, loading


class LoadingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory(prefix='jaydb2-loading-test-')
        cls.output = Path(cls.directory.name)
        cls.shim = cls.output/'loading.so'
        cls.manifest = build_loading.build(cls.shim)
        cls.runtime = loading.Runtime.load(cls.shim, manifest=cls.manifest)
        cls.baseline_owners=set(cls.runtime.live_owners)
        cls.target = cls.output/'target.so'
        subprocess.run([str(build_loading.COMPILER), '-shared', '-fPIC', '-O2',
                        str(ROOT/'tests/service/loading_fixture.c'), '-o', str(cls.target)], check=True)

    @classmethod
    def tearDownClass(cls):
        if set(cls.runtime.live_owners)-cls.baseline_owners:
            raise AssertionError('Tests left unresolved target references')
        cls.directory.cleanup()

    @property
    def pending_owners(self):
        return tuple(owner for owner in self.runtime.live_owners
                     if owner not in self.baseline_owners)

    def setUp(self):
        self.counter = C.c_uint64()
        self.path = os.fsencode(self.output/(self._testMethodName+'.log'))

    def owner(self, *, signal_number=0, delay=0):
        owner = loading.LibraryOwner.open(self.runtime, self.target)
        self.addCleanup(owner.close)
        library = owner.library
        library.loading_fixture_configure.argtypes = [C.c_char_p, C.POINTER(C.c_uint64), C.c_int, C.c_uint]
        library.loading_fixture_configure.restype = None
        library.loading_fixture_value.argtypes = []
        library.loading_fixture_value.restype = C.c_int
        library.loading_fixture_configure(self.path, C.byref(self.counter), signal_number, delay)
        return owner

    def probe(self, body):
        header = ('import sys, ctypes as C, json, os, signal, resource\n'
                  'from pathlib import Path\n'
                  'resource.setrlimit(resource.RLIMIT_CORE, (0, 0))\n'
                  'sys.path.insert(0, '+repr(str(ROOT))+')\n'
                  'from tools.service import loading, build_loading\n'
                  'from unittest import mock\n'
                  'shim=Path('+repr(str(self.shim))+')\n'
                  'target=Path('+repr(str(self.target))+')\n')
        return subprocess.run([sys.executable, '-B', '-c', header+body], cwd=ROOT,
                              check=True, capture_output=True, text=True, timeout=30)

    def test_normal_close_uses_real_destructor_once_and_is_idempotent(self):
        owner = self.owner()
        self.assertEqual(owner.library.loading_fixture_value(), 73)
        self.assertEqual(owner.open_receipt, loading.Receipt(1, True, True, 0, owner.library._handle))
        owner.close()
        self.assertEqual(self.counter.value, 1)
        self.assertIsNone(owner.library)
        self.assertEqual(owner.close_receipt, loading.Receipt(1, True, True, 0))
        with mock.patch.object(self.runtime, '_close', side_effect=AssertionError('second close')):
            owner.close()
        self.assertEqual(self.counter.value, 1)
        self.assertEqual(Path(os.fsdecode(self.path)).read_text(), 'closed\n')

    def test_exception_before_close_c_retains_reference_and_allows_retry(self):
        owner = self.owner()
        with mock.patch.object(self.runtime, '_close', side_effect=MemoryError('before C')):
            with self.assertRaisesRegex(MemoryError, 'before C'):
                owner.close()
        self.assertFalse(owner.close_receipt.entered)
        self.assertFalse(owner.closed)
        self.assertIn(owner, self.pending_owners)
        self.assertEqual(owner.library.loading_fixture_value(), 73)
        self.assertEqual(self.counter.value, 0)
        owner.close()
        self.assertEqual(self.counter.value, 1)

    def test_exception_after_real_close_c_cannot_retry_consumed_reference(self):
        owner = self.owner()
        real = self.runtime._close
        calls = []
        def interrupted(*args):
            calls.append(real(*args))
            raise RuntimeError('after actual dlclose')
        with mock.patch.object(self.runtime, '_close', interrupted):
            with self.assertRaisesRegex(RuntimeError, 'after actual dlclose'):
                owner.close()
            self.assertIsNone(owner.library)
            owner.close()
        self.assertEqual(calls, [loading.OK])
        self.assertEqual(self.counter.value, 1)
        self.assertNotIn(owner, self.pending_owners)

    def test_real_sigalrm_dispatched_after_close_preserves_c_receipt(self):
        # libdl executes the target destructor, which raises a REAL signal. The
        # Python exception is dispatched after the shim has recorded dlclose.
        owner = self.owner(signal_number=signal.SIGALRM)
        old = signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(KeyboardInterrupt('SIGALRM')))
        try:
            with self.assertRaisesRegex(KeyboardInterrupt, 'SIGALRM'):
                owner.close()
            self.assertTrue(owner.closed)
            self.assertIsNone(owner.library)
            self.assertTrue(owner.close_receipt.returned)
            self.assertEqual(self.counter.value, 1)
            owner.close()
        finally:
            signal.signal(signal.SIGALRM, old)

    def test_property_uses_receipt_even_if_python_retirement_fails(self):
        owner = self.owner()
        stale = owner.library
        with mock.patch.object(loading.Runtime, '_retire', side_effect=MemoryError('post-C bookkeeping')):
            with self.assertRaisesRegex(MemoryError, 'post-C bookkeeping'):
                owner.close()
        self.assertIs(owner._library, stale)
        self.assertIsNone(owner.library)
        self.assertEqual(self.counter.value, 1)
        owner.close()

    def test_multiple_owners_same_dso_hold_one_reference_each(self):
        first = self.owner()
        second = self.owner()
        self.assertEqual(first.open_receipt.handle, second.open_receipt.handle)
        first.close()
        self.assertEqual(self.counter.value, 0)
        self.assertEqual(second.library.loading_fixture_value(), 73)
        first.close()
        self.assertEqual(self.counter.value, 0)
        second.close()
        self.assertEqual(self.counter.value, 1)
        third = self.owner()  # a fresh load generation after real unloading
        third.close()
        self.assertEqual(self.counter.value, 2)

    def test_target_open_by_memfd_path_preserves_fd_origin(self):
        fd = os.memfd_create('jaydb2-loading-target', os.MFD_CLOEXEC)
        try:
            with os.fdopen(os.dup(fd), 'wb') as stream:
                stream.write(self.target.read_bytes())
            owner = loading.LibraryOwner.open(self.runtime, '/proc/self/fd/'+str(fd))
            self.addCleanup(owner.close)
            library = owner.library
            library.loading_fixture_configure.argtypes = [C.c_char_p, C.POINTER(C.c_uint64), C.c_int, C.c_uint]
            library.loading_fixture_configure(self.path, C.byref(self.counter), 0, 0)
        finally:
            os.close(fd)
        self.assertEqual(library.loading_fixture_value(), 73)
        owner.close()
        self.assertEqual(self.counter.value, 1)
        self.assertIsNone(owner.library)

    def test_close_in_progress_refuses_retry_and_c_also_refuses(self):
        owner = self.owner(delay=150000)
        failures = []
        def close():
            try:
                owner.close()
            except BaseException as error:
                failures.append(error)
        thread = threading.Thread(target=close)
        thread.start()
        try:
            deadline = time.monotonic()+5
            while not owner.close_receipt.entered and time.monotonic() < deadline:
                time.sleep(.001)
            self.assertTrue(owner.close_receipt.entered)
            self.assertFalse(owner.close_receipt.returned)
            with self.assertRaises(loading.UncertainOperation):
                owner.close()
            self.assertEqual(self.runtime._close(C.byref(owner._opened), C.byref(owner._closed)),
                             loading.UNCERTAIN)
            with self.assertRaises(loading.UncertainOperation):
                _ = owner.library
        finally:
            thread.join(5)
        self.assertFalse(thread.is_alive())
        self.assertEqual(failures, [])
        self.assertEqual(self.counter.value, 1)
        owner.close()

    def test_exception_after_real_open_closes_acquired_reference(self):
        # Preexisting owner makes the destructor observable after the exceptional
        # second acquisition has been cleaned. A leaked second ref prevents it.
        first = self.owner()
        real = self.runtime._open
        def interrupted(*args):
            self.assertEqual(real(*args), loading.OK)
            raise MemoryError('after real dlopen')
        with mock.patch.object(self.runtime, '_open', interrupted):
            with self.assertRaisesRegex(MemoryError, 'after real dlopen'):
                loading.LibraryOwner.open(self.runtime, self.target)
        self.assertEqual(len(self.pending_owners), 1)
        first.close()
        self.assertEqual(self.counter.value, 1)

    def test_real_sigalrm_at_open_return_cleans_recorded_acquisition(self):
        target = self.output/'signal-open.so'
        logfile = self.output/'signal-open.log'
        subprocess.run([str(build_loading.COMPILER), '-shared', '-fPIC', '-O2',
                        '-DJAYDB_LOADING_SIGNAL_OPEN', '-DJAYDB_LOADING_FIXED_LOG="'+str(logfile)+'"',
                        str(ROOT/'tests/service/loading_fixture.c'), '-o', str(target)], check=True)
        def interrupted(*_):
            raise KeyboardInterrupt('real open signal')
        old = signal.signal(signal.SIGALRM, interrupted)
        try:
            with self.assertRaisesRegex(KeyboardInterrupt, 'real open signal'):
                loading.LibraryOwner.open(self.runtime, target)
            self.assertEqual(self.pending_owners, ())
            self.assertEqual(logfile.read_text(), 'closed\n')
        finally:
            signal.signal(signal.SIGALRM, old)

    def test_open_in_progress_cannot_be_closed_or_retried(self):
        target = self.output/'slow-open.so'
        subprocess.run([str(build_loading.COMPILER), '-shared', '-fPIC', '-O2',
                        '-DJAYDB_LOADING_OPEN_DELAY=150000',
                        str(ROOT/'tests/service/loading_fixture.c'), '-o', str(target)], check=True)
        owners, failures = [], []
        def open_library():
            try:
                owners.append(loading.LibraryOwner.open(self.runtime, target))
            except BaseException as error:
                failures.append(error)
        thread = threading.Thread(target=open_library)
        thread.start()
        try:
            deadline = time.monotonic()+5
            while not self.pending_owners and time.monotonic() < deadline:
                time.sleep(.001)
            pending, = self.pending_owners
            self.assertTrue(pending.open_receipt.entered)
            self.assertFalse(pending.open_receipt.returned)
            with self.assertRaises(loading.UncertainOperation):
                pending.close()
            self.assertEqual(self.runtime._open(pending._path, os.RTLD_NOW, C.byref(pending._opened)),
                             loading.UNCERTAIN)
            self.assertEqual(self.runtime._close(C.byref(pending._opened), C.byref(pending._closed)),
                             loading.UNCERTAIN)
            self.assertFalse(pending.close_receipt.entered)
        finally:
            thread.join(5)
            for owner in owners:
                owner.close()
        self.assertFalse(thread.is_alive())
        self.assertEqual(failures, [])
        self.assertTrue(pending.closed)

    def test_preentry_owner_remains_retained_during_runtime_inspection(self):
        entered, proceed = threading.Event(), threading.Event()
        owners, failures = [], []
        real = self.runtime._open
        def paused(*args):
            entered.set()
            if not proceed.wait(5):
                raise TimeoutError('test open gate')
            return real(*args)
        def open_library():
            try:
                owners.append(loading.LibraryOwner.open(self.runtime, self.target))
            except BaseException as error:
                failures.append(error)
        with mock.patch.object(self.runtime, '_open', paused):
            thread = threading.Thread(target=open_library)
            thread.start()
            try:
                self.assertTrue(entered.wait(5))
                pending, = self.pending_owners
                self.assertFalse(pending.open_receipt.entered)
                self.assertEqual(self.pending_owners, (pending,))
                with self.assertRaises(loading.UncertainOperation):
                    pending.close()
            finally:
                proceed.set()
                thread.join(5)
                for owner in owners:
                    owner.close()
        self.assertFalse(thread.is_alive())
        self.assertEqual(failures, [])
        self.assertTrue(pending.closed)

    def test_c_open_replay_does_not_acquire_another_reference(self):
        owner = self.owner()
        self.assertEqual(self.runtime._open(owner._path, os.RTLD_NOW, C.byref(owner._opened)), loading.OK)
        owner.close()
        self.assertEqual(self.counter.value, 1)

    def test_non_consuming_close_error_fixture_retains_owner_and_retries(self):
        # Python-side error-path fixture. No libdl call/consumption occurs on
        # this injected error. The retry then executes the REAL C/libdl close.
        owner = self.owner()
        def no_consumption(opened, closed):
            receipt = C.cast(closed, C.POINTER(loading._CloseReceipt)).contents
            receipt.entered = 1
            receipt.outcome = (0xffffffff << 32) | 1
            return loading.DL_ERROR
        with mock.patch.object(self.runtime, '_close', no_consumption):
            with self.assertRaises(loading.CloseError):
                owner.close()
        self.assertEqual(owner.close_receipt.status, -1)
        self.assertTrue(owner.close_receipt.returned)
        self.assertIn(owner, self.pending_owners)
        self.assertEqual(self.counter.value, 0)
        self.assertEqual(owner.library.loading_fixture_value(), 73)
        owner.close()
        self.assertEqual(self.counter.value, 1)

    def test_c_non_consuming_error_fixture_records_status_before_retry(self):
        # Compile a separate TEST shim with --wrap=dlclose. The first call is
        # synthetic failure, and the second is real libdl. The production build
        # has no wrap/test symbols. No invalid target handle is manufactured.
        shim = self.output/'wrapped-close.so'
        subprocess.run([str(build_loading.COMPILER), '-shared', '-fPIC', '-std=c11', '-O2',
                        '-DJAYDB_LOADING_WRAP_DLCLOSE', '-DJAYDB_LOADING_BUILD_ID="'+('f'*64)+'"',
                        '-Wl,-z,nodelete', '-Wl,--wrap=dlclose',
                        str(ROOT/'tools/service/loading.c'),
                        str(ROOT/'tests/service/loading_fixture.c'), '-ldl', '-o', str(shim)], check=True)
        self.probe('wrapped=C.CDLL('+repr(str(shim))+')\n'+"""
wrapped.jaydb_loading_open_v1.argtypes=[C.c_char_p,C.c_int,C.POINTER(loading._OpenReceipt)]
wrapped.jaydb_loading_close_v1.argtypes=[C.POINTER(loading._OpenReceipt),C.POINTER(loading._CloseReceipt)]
wrapped.loading_fixture_close_calls.restype=C.c_uint
opened=loading._OpenReceipt(abi=1)
closed=loading._CloseReceipt(abi=1)
assert wrapped.jaydb_loading_open_v1(os.fsencode(target),os.RTLD_NOW,C.byref(opened))==loading.OK
library=C.CDLL(str(target),handle=opened.handle)
counter=C.c_uint64()
library.loading_fixture_configure.argtypes=[C.c_char_p,C.POINTER(C.c_uint64),C.c_int,C.c_uint]
library.loading_fixture_configure(None,C.byref(counter),0,0)
assert wrapped.jaydb_loading_close_v1(C.byref(opened),C.byref(closed))==loading.DL_ERROR
receipt=loading._receipt(closed)
assert receipt.entered and receipt.returned and receipt.status==-1
assert counter.value==0 and library.loading_fixture_value()==73
assert wrapped.jaydb_loading_close_v1(C.byref(opened),C.byref(closed))==loading.OK
assert counter.value==1 and loading._closed(closed)
assert wrapped.jaydb_loading_close_v1(C.byref(opened),C.byref(closed))==loading.OK
assert counter.value==1 and wrapped.loading_fixture_close_calls()==2
""")

    def test_exception_before_open_c_acquires_nothing(self):
        with mock.patch.object(self.runtime, '_open', side_effect=MemoryError('before open')):
            with self.assertRaisesRegex(MemoryError, 'before open'):
                loading.LibraryOwner.open(self.runtime, self.target)
        self.assertEqual(self.pending_owners, ())

    def test_cdll_handle_wrapper_failure_releases_acquired_reference(self):
        first = self.owner()
        real = C.CDLL
        def fail_attach(*args, **kwargs):
            self.assertTrue(kwargs.get('handle'))
            raise MemoryError('CDLL wrapper setup')
        with mock.patch.object(C, 'CDLL', fail_attach):
            with self.assertRaisesRegex(MemoryError, 'CDLL wrapper setup'):
                loading.LibraryOwner.open(self.runtime, self.target)
        self.assertIs(C.CDLL, real)
        self.assertEqual(len(self.pending_owners), 1)
        first.close()
        self.assertEqual(self.counter.value, 1)

    def test_open_setup_cleanup_failure_keeps_owner_available_for_retry(self):
        first = self.owner()
        with mock.patch.object(C, 'CDLL', side_effect=MemoryError('attach')), \
                mock.patch.object(self.runtime, '_close', side_effect=RuntimeError('pre-call close')):
            with self.assertRaisesRegex(MemoryError, 'attach') as error:
                loading.LibraryOwner.open(self.runtime, self.target)
        retained = [owner for owner in self.pending_owners if owner is not first]
        self.assertEqual(len(retained), 1)
        self.assertIn('cleanup unresolved', error.exception.__notes__[0])
        self.assertTrue(retained[0].open_receipt.returned)
        self.assertFalse(retained[0].close_receipt.entered)
        retained[0].close()
        first.close()
        self.assertEqual(self.counter.value, 1)

    def test_missing_target_is_real_open_failure_with_no_owner_leak(self):
        with self.assertRaises(loading.OpenError):
            loading.LibraryOwner.open(self.runtime, self.output/'does-not-exist.so')
        self.assertEqual(self.pending_owners, ())

    def test_runtime_retains_lost_owner_until_explicit_close(self):
        owner = self.owner()
        reference = weakref.ref(owner)
        # addCleanup above deliberately also holds this owner. Remove that
        # cleanup to isolate the runtime's own strong reference.
        self._cleanups.pop()
        del owner
        self.assertIsNotNone(reference())
        retained, = self.pending_owners
        retained.close()
        self.assertEqual(self.counter.value, 1)
        del retained
        self.assertIsNone(reference())

    def test_repeated_runtime_install_reuses_one_bootstrap_reference(self):
        with mock.patch.object(C, 'CDLL', side_effect=AssertionError('extra bootstrap')):
            for _ in range(10):
                self.assertIs(loading.Runtime.load(self.shim, manifest=self.manifest), self.runtime)
        with self.assertRaises(AttributeError):
            self.runtime.identity = None
        with self.assertRaises(dataclasses.FrozenInstanceError):
            self.runtime.identity.abi = 2

    def test_hash_or_manifest_abi_mismatch_rejected_before_load(self):
        for field, value in [('moduleSha256', '0'*64), ('abiVersion', 2),
                             ('nodelete', False), ('openReceiptBytes', 1)]:
            with self.subTest(field=field):
                report = {**self.manifest, field: value}
                with self.assertRaises(loading.IdentityMismatch):
                    loading.Runtime.load(self.shim, manifest=report)

    def test_json_alone_cannot_grant_loaded_build_identity(self):
        self.probe("""
report=json.loads(shim.with_suffix('.so.json').read_text())
report['buildIdentitySha256']='0'*64
try:
    loading.Runtime.load(shim, manifest=report)
except loading.IdentityMismatch as e:
    assert 'Loaded loading descriptor' in str(e), str(e)
else:
    raise AssertionError('JSON granted a different identity')
""")

    def test_old_dlopen_mapping_rejected_after_atomic_same_path_rebuild(self):
        self.probe("""
import tempfile, shutil
with tempfile.TemporaryDirectory() as work:
    work=Path(work)
    source=work/'sources'
    source.mkdir()
    for name in ('loading.c','loading.h','build_loading.py'):
        shutil.copyfile(build_loading.SOURCE/name, source/name)
    build_loading.SOURCE=source
    output=work/'runtime.so'
    first=build_loading.build(output)
    old=C.CDLL(str(output), mode=os.RTLD_NOW|os.RTLD_LOCAL|os.RTLD_NODELETE)
    with (source/'loading.c').open('a') as f:
        f.write('\\n/* Distinct build, same ABI. */\\n')
    second=build_loading.build(output)
    assert first['buildIdentitySha256'] != second['buildIdentitySha256']
    assert first['moduleSha256'] != second['moduleSha256']
    try:
        loading.Runtime.load(output, manifest=second)
    except loading.IdentityMismatch as e:
        assert 'Loaded loading descriptor' in str(e), str(e)
    else:
        raise AssertionError('old mapped descriptor accepted new report')
    old.jaydb_loading_describe_v1.restype=C.POINTER(loading._Descriptor)
    assert bytes(old.jaydb_loading_describe_v1().contents.build_identity).decode()==first['buildIdentitySha256']
""")

    def test_exceptional_bootstrap_is_single_reserved_attempt(self):
        self.probe("""
real=C.CDLL
calls=[]
def interrupted(*args, **kwargs):
    calls.append(real(*args, **kwargs))
    raise MemoryError('after real shim dlopen')
with mock.patch.object(C, 'CDLL', interrupted):
    try:
        loading.Runtime.load(shim)
    except MemoryError:
        pass
    else:
        raise AssertionError('missing injected failure')
    try:
        loading.Runtime.load(shim)
    except loading.InstallationError:
        pass
    else:
        raise AssertionError('uncertain bootstrap retried')
assert len(calls)==1
""")

    def test_runtime_can_be_explicitly_installed_from_memfd_and_pinned_manifest(self):
        self.probe("""
report=json.loads(shim.with_suffix('.so.json').read_text())
fd=os.memfd_create('loader-baseline',os.MFD_CLOEXEC)
with os.fdopen(os.dup(fd),'wb') as stream:
    stream.write(shim.read_bytes())
runtime=loading.Runtime.load('/proc/self/fd/'+str(fd),manifest=report)
os.close(fd)
owner=loading.LibraryOwner.open(runtime,target)
assert owner.library.loading_fixture_value()==73
owner.close()
assert owner.closed and owner.library is None and runtime.live_owners==()
""")

    def test_different_runtime_identity_requires_new_process(self):
        report = {**self.manifest, 'buildIdentitySha256': '0'*64}
        with self.assertRaisesRegex(loading.IdentityMismatch, 'fixed for this process'):
            loading.Runtime.load(self.shim, manifest=report)

    def test_production_elf_is_nodelete_and_exports_only_three_functions(self):
        dynamic = subprocess.check_output(['readelf', '-d', str(self.shim)], text=True)
        self.assertIn('NODELETE', dynamic)
        symbols = subprocess.check_output(['nm', '-D', '--defined-only', str(self.shim)], text=True)
        self.assertEqual(sorted(line.split()[-1] for line in symbols.splitlines()),
                         ['jaydb_loading_close_v1', 'jaydb_loading_describe_v1', 'jaydb_loading_open_v1'])
        self.assertNotIn('fixture', symbols)
        self.assertEqual(self.manifest['moduleSha256'], hashlib.sha256(self.shim.read_bytes()).hexdigest())


if __name__ == '__main__':
    unittest.main()
