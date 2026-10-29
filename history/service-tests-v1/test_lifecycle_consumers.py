"""Real consumer ownership across interruption; payload/coverage are fixtures.

The C fixture actually allocates/frees output and logs at unload. These tests
do not certify Bend semantics or turn synthetic windows into MedicaoReal.
"""
import ctypes as C
import gc
import hashlib
import inspect
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
from types import SimpleNamespace
import unittest
from unittest.mock import patch
import weakref
from contextlib import contextmanager

from tools.service.abi import Module, NativeOwnershipPending
from tools.service import controller
from tools.service.lifecycle import LifecycleRuntime, ProcessOwner
from tools.native.accounted import install_accounted
from tests.service.runtime_profile import fixture_lifecycle
from tests.service.test_completion import CompletionTests
from tools.service.build_commit import build as build_commit

ROOT=Path(__file__).resolve().parents[2]

class Stats(C.Structure):
    _fields_=[(n,C.c_uint64) for n in
        ('runs','allocations','releases','release_calls','destructors','live_at_destructor')]


@contextmanager
def signal_at_line(function,text,*,condition=lambda frame:True):
    lines,start=inspect.getsourcelines(function)
    target=start+next(i for i,line in enumerate(lines) if text in line)
    fired=[]
    def trace(frame,event,arg):
        if (not fired and event=='line' and frame.f_code is function.__code__
                and frame.f_lineno==target and condition(frame)):
            fired.append(target)
            signal.raise_signal(signal.SIGALRM)
        return trace
    def interrupt(*_):raise RuntimeError('real registry SIGALRM')
    previous=signal.signal(signal.SIGALRM,interrupt)
    sys.settrace(trace)
    try:yield fired
    finally:
        sys.settrace(None)
        signal.signal(signal.SIGALRM,previous)


class LifecycleConsumers(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.runtime=fixture_lifecycle()
        cls.temp=tempfile.TemporaryDirectory(prefix='jaydb-lifecycle-consumers-')
        cls.folder=Path(cls.temp.name)
        cls.module_path=cls.folder/'native.so'
        cls.library=cls.folder/'commit.so'
        build_commit(cls.library,test_fixture=ROOT/'tests/service/commit_fixture.c')
        subprocess.run(['/usr/bin/clang-19','-shared','-fPIC','-O2','-Wall','-Wextra','-Werror',
            str(ROOT/'tests/service/lifecycle_consumer_fixture.c'),'-o',str(cls.module_path)],check=True)
        cls.module_path.with_suffix('.so.json').write_text(json.dumps({
            'moduleSha256':hashlib.sha256(cls.module_path.read_bytes()).hexdigest(),
            'sourceSha256':'a'*64,'imageBytes':4096,'ownedOutputV3':True,
            'demandStableHeapV3':True,'durationBitsV3':128,'absoluteSetupDeadlineV3':True,
            'automaticTermStackV3':True,'automaticNativeStackV3':True,
            'automaticNativeStackModeV3':'linux-main-growdown','nativeStackClashProtection':True}))
        install_accounted(Module)

    @classmethod
    def tearDownClass(cls):
        assert not cls.runtime.live_processes, cls.runtime.live_processes
        assert not cls.runtime.live_leases, cls.runtime.live_leases
        cls.temp.cleanup()

    def module(self,*,release_error=0,signal_release=0,signal_run=0):
        m=Module(self.module_path,lifecycle_runtime=self.runtime)
        stats=Stats()
        configure=m.library.lifecycle_fixture_configure
        configure.argtypes=[C.POINTER(Stats),C.c_char_p,C.c_uint32,C.c_uint32,C.c_int,C.c_int,C.c_uint]
        configure(C.byref(stats),None,release_error,0,signal_release,signal_run,0)
        self.addCleanup(m.close)
        return m,stats

    def run_module(self,m,*,accounted=False):
        deadline=time.monotonic_ns()+10**10
        options=dict(capacity=100,memory=100,timeout_ns=10**10,setup_deadline_ns=deadline)
        if accounted:
            return m.run_accounted(b'',accounting=SimpleNamespace(scope=1,ceiling=100,poll=lambda:None),**options)
        return m.run(b'',**options)

    def test_normal_and_accounted_calls_release_before_real_unload(self):
        for accounted in (False,True):
            with self.subTest(accounted=accounted):
                m,s=self.module()
                self.assertEqual(self.run_module(m,accounted=accounted),b'leased!')
                self.assertEqual((s.allocations,s.releases),(1,1))
                m.close()
                self.assertEqual((s.destructors,s.live_at_destructor),(1,0))

    def test_preentry_release_failure_retains_result_and_prevents_unload(self):
        for accounted in (False,True):
            with self.subTest(accounted=accounted):
                m,s=self.module()
                with patch.object(self.runtime,'_release',side_effect=MemoryError('before C release')):
                    with self.assertRaises(NativeOwnershipPending):self.run_module(m,accounted=accounted)
                    with self.assertRaises(NativeOwnershipPending):m.close()
                self.assertEqual((s.allocations,s.releases,s.destructors),(1,0,0))
                pending,=self.runtime.live_leases
                self.assertEqual(pending.native_result.lease,17)
                self.assertIs(pending.library_owner,m._library_owner)
                m.close()
                self.assertEqual((s.releases,s.destructors,s.live_at_destructor),(1,1,0))

    def test_lost_module_still_has_recoverable_result_and_dso_owner(self):
        m,s=self.module()
        self._cleanups.pop()
        ref=weakref.ref(m)
        with patch.object(self.runtime,'_release',side_effect=MemoryError('retain')):
            with self.assertRaises(NativeOwnershipPending):self.run_module(m)
        owner,=self.runtime.live_leases
        del m;gc.collect()
        self.assertIsNone(ref())
        self.assertEqual(s.destructors,0)
        owner.release();owner.library_owner.close()
        self.assertEqual((s.releases,s.destructors,s.live_at_destructor),(1,1,0))

    def test_return_exception_after_release_never_repeats_consumption(self):
        m,s=self.module()
        release=self.runtime._release
        def interrupted(*args):
            release(*args)
            raise MemoryError('after consumed C receipt')
        with patch.object(self.runtime,'_release',interrupted):
            with self.assertRaises(MemoryError):self.run_module(m)
        self.assertFalse(self.runtime.live_leases)
        with patch.object(self.runtime,'_release',side_effect=AssertionError('double release')):m.close()
        self.assertEqual((s.release_calls,s.releases,s.live_at_destructor),(1,1,0))

    def test_accounted_receipt_allocation_failure_still_releases_output(self):
        from tools.native.accounted import Receipt
        m,s=self.module()
        with patch.object(Receipt,'read',side_effect=MemoryError('receipt wrapper')):
            with self.assertRaises(MemoryError):self.run_module(m,accounted=True)
        self.assertEqual((s.allocations,s.releases),(1,1))
        self.assertFalse(self.runtime.live_leases)
        m.close()
        self.assertEqual((s.destructors,s.live_at_destructor),(1,0))

    def test_real_signals_at_run_and_release_return_preserve_ownership(self):
        def interrupt(*_):raise RuntimeError('real native SIGALRM')
        previous=signal.signal(signal.SIGALRM,interrupt)
        try:
            for accounted in (False,True):
                for at_run in (False,True):
                    with self.subTest(accounted=accounted,at_run=at_run):
                        m,s=self.module(signal_run=signal.SIGALRM if at_run else 0,
                                        signal_release=0 if at_run else signal.SIGALRM)
                        with self.assertRaisesRegex(RuntimeError,'real native'):
                            self.run_module(m,accounted=accounted)
                        m.close()
                        self.assertEqual((s.releases,s.destructors,s.live_at_destructor),(1,1,0))
        finally:signal.signal(signal.SIGALRM,previous)

    def test_nonconsuming_release_error_can_retry_before_unload(self):
        m,s=self.module(release_error=2)
        with self.assertRaises(NativeOwnershipPending):self.run_module(m)
        self.assertEqual((s.releases,s.destructors),(0,0))
        m.close()
        self.assertEqual((s.release_calls,s.releases,s.destructors,s.live_at_destructor),(2,1,1,0))

    def test_sigalrm_after_real_spawn_before_python_assignment_kills_and_reaps(self):
        start=self.runtime._start
        captured=[]
        def interrupt(*_):raise RuntimeError('real spawn SIGALRM')
        def interrupted(native,*args):
            code=start(native,*args)
            captured.append(self.runtime.live_processes[0].pid)
            signal.raise_signal(signal.SIGALRM)
            return code
        previous=signal.signal(signal.SIGALRM,interrupt)
        try:
            with patch.object(self.runtime,'_start',interrupted):
                with self.assertRaisesRegex(RuntimeError,'real spawn'):
                    controller.helper([sys.executable,'-I','-S','-c','import time;time.sleep(60)'],
                        time.monotonic_ns()+10**10,100,lifecycle_runtime=self.runtime)
        finally:signal.signal(signal.SIGALRM,previous)
        self.assertEqual(len(captured),1)
        self.assertFalse(Path('/proc',str(captured[0])).exists())
        self.assertFalse(self.runtime.live_processes)

    def test_prepare_return_exception_closes_recorded_pipe_descriptors(self):
        prepare=self.runtime._prepare
        fds=[]
        def interrupted(native):
            prepare(native)
            fds.extend(self.runtime.live_processes[0]._native.fds)
            raise MemoryError('after pipe preparation')
        with patch.object(self.runtime,'_prepare',interrupted):
            with self.assertRaises(MemoryError):
                controller.helper([sys.executable,'-c','print(1)'],time.monotonic_ns()+10**9,100)
        self.assertEqual(len(fds),4)
        for fd in fds:
            with self.assertRaises(OSError):os.fstat(fd)
        self.assertFalse(self.runtime.live_processes)

    def test_unresolved_native_release_does_not_complete_a_public_error(self):
        db,root,counter,completion,*_=CompletionTests.setup_request(self)
        db.bind_request_completion(completion,instrument_deadline_ns=10**30)
        m,s=self.module()
        db.modules['decode']=SimpleNamespace(
            run_accounted=lambda data,**opts:self.run_module(m,accounted=True))
        published=root.native.published
        with patch.object(self.runtime,'_release',side_effect=MemoryError('release pending')):
            with self.assertRaises(NativeOwnershipPending):db.request(b'body')
        self.assertIsNone(root.native.completed)
        self.assertEqual(root.native.published,published)
        self.assertIsNone(completion.prepared)
        self.assertEqual(s.destructors,0)
        m.close()
        self.assertEqual((s.releases,s.destructors,s.live_at_destructor),(1,1,0))

    def test_unresolved_helper_cleanup_is_not_mapped_to_a_public_error(self):
        db,root,counter,completion,*_=CompletionTests.setup_request(self)
        db.bind_request_completion(completion,instrument_deadline_ns=10**30)
        def decode(data,**opts):
            return controller.helper([sys.executable,'-I','-S','-c','import time;time.sleep(60)'],
                time.monotonic_ns()+10**10,100,
                memory_window=SimpleNamespace(ceiling=100,
                    poll=lambda:(_ for _ in ()).throw(RuntimeError('monitor interrupted'))))
        db.modules['decode']=SimpleNamespace(run_accounted=decode)
        published=root.native.published
        owners=()
        try:
            with patch.object(self.runtime,'_close_process',side_effect=MemoryError('cleanup pending')):
                with self.assertRaises(controller.IncompleteIntegration):db.request(b'body')
            owners=self.runtime.live_processes
            self.assertEqual(len(owners),1)
            self.assertIsNone(root.native.completed)
            self.assertEqual(root.native.published,published)
            self.assertIsNone(completion.prepared)
        finally:
            for owner in self.runtime.live_processes:owner.close()
        self.assertTrue(owners[0].closed)

    def test_real_signal_during_helper_owner_enumeration_cannot_complete_error(self):
        db,root,counter,completion,*_=CompletionTests.setup_request(self)
        db.lifecycle_runtime=self.runtime
        db.bind_request_completion(completion,instrument_deadline_ns=10**30)
        def decode(data,**opts):
            return controller.helper([sys.executable,'-I','-S','-c','import time;time.sleep(60)'],
                time.monotonic_ns()+20_000_000,100)
        db.modules['decode']=SimpleNamespace(run_accounted=decode)
        try:
            with signal_at_line(controller.helper,'for owner in runtime.live_processes:') as fired:
                with self.assertRaises(controller.IncompleteIntegration):db.request(b'body')
            self.assertTrue(fired)
            pending,=self.runtime.live_processes
            self.assertFalse(pending.closed)
            self.assertIsNone(os.waitid(os.P_PID,pending.pid,os.WEXITED|os.WNOHANG|os.WNOWAIT))
            self.assertIsNone(root.native.completed)
            self.assertIsNone(completion.prepared)
        finally:
            for owner in self.runtime.live_processes:owner.close()

    def test_real_signal_during_lease_enumeration_cannot_complete_error(self):
        db,root,counter,completion,*_=CompletionTests.setup_request(self)
        db.lifecycle_runtime=self.runtime
        db.bind_request_completion(completion,instrument_deadline_ns=10**30)
        m,s=self.module(release_error=2)
        def during_close(frame):
            return frame.f_back is not None and frame.f_back.f_code is Module.close.__code__
        with patch.object(controller,'build',return_value=(m,db.limits)), \
                signal_at_line(Module._release_outputs,'for owner in runtime.live_leases:',
                    condition=during_close) as fired:
            with self.assertRaises(NativeOwnershipPending):db.request(b'body')
        self.assertTrue(fired)
        self.assertEqual((s.allocations,s.releases,s.destructors),(1,0,0))
        self.assertIsNone(root.native.completed)
        self.assertIsNone(completion.prepared)
        self.assertIsNotNone(m.library)
        m.close()
        self.assertEqual((s.releases,s.destructors,s.live_at_destructor),(1,1,0))

    def test_completion_owner_check_is_outside_the_public_error_mapper(self):
        db,root,counter,completion,*_=CompletionTests.setup_request(self)
        db.lifecycle_runtime=self.runtime
        db.bind_request_completion(completion,instrument_deadline_ns=10**30)
        read=LifecycleRuntime.live_processes.fget
        fail=[False]
        def registry(runtime):
            pending=read(runtime)
            if pending and fail[0]:raise MemoryError('registry cannot be inspected')
            return pending
        def polling():
            fail[0]=True
            raise controller.StageTimeout('real helper cleanup boundary fixture')
        def decode(data,**opts):
            return controller.helper([sys.executable,'-I','-S','-c','import time;time.sleep(60)'],
                time.monotonic_ns()+10**10,100,
                memory_window=SimpleNamespace(ceiling=100,poll=polling))
        db.modules['decode']=SimpleNamespace(run_accounted=decode)
        try:
            with patch.object(LifecycleRuntime,'live_processes',property(registry)):
                with self.assertRaisesRegex(MemoryError,'cannot be inspected'):db.request(b'body')
            self.assertEqual(len(self.runtime.live_processes),1)
            self.assertIsNone(root.native.completed)
            self.assertIsNone(completion.prepared)
        finally:
            for owner in self.runtime.live_processes:owner.close()


if __name__=='__main__':unittest.main(verbosity=2)
