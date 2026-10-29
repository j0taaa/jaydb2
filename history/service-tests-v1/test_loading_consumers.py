"""Causal loader-consumer regressions for completion review F5.

Exceptions after the real close model FFI return dispatch. SIGALRM is also
raised by a real DSO destructor. No released function pointer is called.
"""
import ctypes as C
import json
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

from tools.service import loading
from tools.service.abi import Module
from tools.service.build_commit import build
from tools.service.commit import Root
from tools.service.receiving import Receiver

ROOT=Path(__file__).resolve().parents[2]


class LoadingConsumers(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp=tempfile.TemporaryDirectory(prefix='jaydb-loading-consumers-')
        cls.folder=Path(cls.temp.name)
        cls.commit_path=cls.folder/'commit.so'
        fixture=cls.folder/'commit-loading.c'
        fixture.write_text('#include "'+str(ROOT/'tests/service/loading_fixture.c')+'"\n'
                           '#include "'+str(ROOT/'tests/service/commit_fixture.c')+'"\n')
        cls.report=build(cls.commit_path,test_fixture=fixture)
        root=Root(cls.commit_path,b'published',_test_fixture=True)
        cls.runtime=loading.Runtime.current()
        from tests.service.runtime_profile import fixture_lifecycle
        fixture_lifecycle(cls.runtime)
        cls.baseline_owners=set(cls.runtime.live_owners)
        root.close()
        cls.target=cls.folder/'target.so'
        subprocess.run(['/usr/bin/clang-19','-O2','-fPIC','-shared',
            str(ROOT/'tests/service/loading_fixture.c'),'-o',str(cls.target)],check=True)

    @classmethod
    def tearDownClass(cls):
        if set(cls.runtime.live_owners)-cls.baseline_owners:
            raise AssertionError('Unresolved test library owners beyond the fixed runtime baseline')
        cls.temp.cleanup()

    def root(self):
        root=Root(self.commit_path,b'published',_test_fixture=True)
        self.addCleanup(root.close)
        return root

    def consumer(self,kind):
        # Only close/library are exercised in these two fixtures. Normal
        # constructors are separately covered by receiving/native ABI tests.
        instance=kind.__new__(kind)
        instance._library_owner=loading.LibraryOwner.open(self.runtime,self.target)
        self.addCleanup(instance.close)
        return instance

    def configure(self,consumer,number=0):
        count=C.c_uint64()
        f=consumer.library.loading_fixture_configure
        f.argtypes=[C.c_char_p,C.POINTER(C.c_uint64),C.c_int,C.c_uint]
        f(None,C.byref(count),number,0)
        return count

    def test_root_real_close_then_return_exception_never_retries_dlclose(self):
        root=self.root();count=self.configure(root)
        root.prepare(b'abandoned',state=b'never published')
        close=self.runtime._close
        def interrupted(*args):
            close(*args)
            raise RuntimeError('after actual dlclose')
        with patch.object(self.runtime,'_close',interrupted):
            with self.assertRaisesRegex(RuntimeError,'after actual'):root.close()
        self.assertEqual(count.value,1)
        self.assertIsNone(root.library)
        self.assertEqual(root._records,{})
        self.assertTrue(root.stack.closed)
        with patch.object(self.runtime,'_close',side_effect=AssertionError('double close')):
            root.close()

    def test_sigalrm_from_root_destructor_preserves_successful_close_receipt(self):
        root=self.root();count=self.configure(root,signal.SIGALRM)
        def handler(*unused):raise RuntimeError('real destructor signal')
        previous=signal.signal(signal.SIGALRM,handler)
        try:
            with self.assertRaisesRegex(RuntimeError,'real destructor signal'):root.close()
        finally:signal.signal(signal.SIGALRM,previous)
        self.assertEqual(count.value,1)
        self.assertTrue(root._library_owner.closed)
        self.assertIsNone(root.library)
        root.close()

    def test_module_and_receiver_read_durable_close_after_return_exception(self):
        for kind in (Module,Receiver):
            with self.subTest(kind=kind.__name__):
                consumer=self.consumer(kind);count=self.configure(consumer)
                close=self.runtime._close
                def interrupted(*args):
                    close(*args)
                    raise MemoryError('return dispatch')
                with patch.object(self.runtime,'_close',interrupted):
                    with self.assertRaises(MemoryError):consumer.close()
                self.assertIsNone(consumer.library)
                self.assertEqual(count.value,1)
                with patch.object(self.runtime,'_close',side_effect=AssertionError('double close')):
                    consumer.close()

    def test_module_and_receiver_real_sigalrm_after_dlclose(self):
        def handler(*unused):raise RuntimeError('actual destructor')
        previous=signal.signal(signal.SIGALRM,handler)
        try:
            for kind in (Module,Receiver):
                consumer=self.consumer(kind);count=self.configure(consumer,signal.SIGALRM)
                with self.assertRaisesRegex(RuntimeError,'actual destructor'):consumer.close()
                self.assertIsNone(consumer.library)
                self.assertEqual(count.value,1)
                consumer.close()
        finally:signal.signal(signal.SIGALRM,previous)

    def test_preentry_close_failure_retains_root_owner_for_cleanup(self):
        root=self.root();count=self.configure(root)
        with patch.object(self.runtime,'_close',side_effect=MemoryError('before C')):
            with self.assertRaises(MemoryError):root.close()
        self.assertFalse(root._library_owner.close_receipt.entered)
        self.assertIsNotNone(root.library)
        self.assertEqual(count.value,0)
        with self.assertRaisesRegex(RuntimeError,'closed'):_=root.state
        root.close()
        self.assertEqual(count.value,1)

    def test_stack_cleanup_error_still_attempts_independent_library_release(self):
        root=self.root();count=self.configure(root)
        held=memoryview(root.stack)
        try:
            with self.assertRaises(BufferError):root.close()
            self.assertEqual(count.value,1)
            self.assertIsNone(root.library)
        finally:held.release()
        root.close()
        self.assertTrue(root.stack.closed)

    def test_module_constructor_failure_releases_acquired_reference(self):
        report={'moduleSha256':__import__('hashlib').sha256(self.target.read_bytes()).hexdigest(),
                'ownedOutputV3':True,'demandStableHeapV3':True,'durationBitsV3':128}
        self.target.with_suffix('.so.json').write_text(json.dumps(report))
        before=self.runtime.live_owners
        with self.assertRaises(AttributeError):Module(self.target,loading_runtime=self.runtime)
        self.assertEqual(self.runtime.live_owners,before)

    def test_runtime_is_explicit_and_never_built_by_module(self):
        code=('from tools.service.loading import Runtime,InstallationError\n'
              'try:Runtime.current()\n'
              'except InstallationError:pass\n'
              'else:raise AssertionError("implicit installation")\n')
        subprocess.run([sys.executable,'-B','-c',code],cwd=ROOT,check=True)

    def test_paired_manifest_is_checked_even_when_runtime_is_already_installed(self):
        from tools.service.paired_loading import runtime_for
        report={**self.report,'loading':{'file':self.report['loading']['file'],
            'manifest':{**self.report['loading']['manifest'],'moduleSha256':'0'*64}}}
        with self.assertRaisesRegex(ValueError,'hash'):
            runtime_for(self.commit_path,report)

if __name__=='__main__':unittest.main()
