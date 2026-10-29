"""Causal regressions for the independent completion_v1 review.

Complete observations below are explicit numerical fixtures. Resource/return
failure injection verifies ownership; it does not manufacture FalhaReal.
"""
from __future__ import annotations
from dataclasses import FrozenInstanceError
import ctypes as C
import gc
import inspect
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

from tools.service import commit,controller
from tools.service.build_commit import build
from tools.service.commit import Root
from tools.service.lifecycle import ProcessOwner
from tests.service.runtime_profile import fixture_lifecycle
from tools.service.frames import error_frame
from tests.service import test_completion as fixtures

ROOT=Path(__file__).resolve().parents[2]

class CompletionReviewTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp=tempfile.TemporaryDirectory(prefix='jaydb-completion-review-fixes-')
        cls.library=Path(cls.temp.name)/'commit.so'
        build(cls.library,test_fixture=ROOT/'tests/service/commit_fixture.c')
        cls.lifecycle=fixture_lifecycle()
    @classmethod
    def tearDownClass(cls):cls.temp.cleanup()

    def root(self):
        root=Root(self.library,b'published',_test_fixture=True)
        self.addCleanup(root.close)
        root.library.jaydb_commit_fixture.argtypes=[C.c_uint64]*8
        root.library.jaydb_commit_fixture(9,1,40,100,100,0,0,0)
        return root

    def test_prepared_public_fields_and_native_view_are_immutable(self):
        root=self.root()
        prepared=root.prepare(b'ready',state=b'new',with_limit=True)
        for name,value in (('state',b'forged'),('response',error_frame('falha')),('limited',None)):
            with self.subTest(name=name):
                with self.assertRaises(FrozenInstanceError):setattr(prepared,name,value)
        with self.assertRaises(FrozenInstanceError):prepared.native.publish=0
        with self.assertRaises(FrozenInstanceError):root.native.published=prepared.address
        root.finish_or_limit(prepared,scope=1,ceiling=100,deadline_ns=101,instrument_deadline_ns=200)
        with self.assertRaises(FrozenInstanceError):prepared.state=b'unpublished'
        self.assertEqual(root.state,b'new')
        self.assertEqual(C.string_at(prepared.native.state,prepared.native.state_bytes),b'new')

    def test_error_cannot_be_changed_into_equal_state_publication(self):
        root=self.root();before=root.native.published
        prepared=root.prepare(error_frame('falha'),with_limit=True)
        with self.assertRaises(FrozenInstanceError):prepared.native.publish=1
        root.finish_or_limit(prepared,scope=1,ceiling=100,deadline_ns=101,instrument_deadline_ns=200)
        self.assertEqual(root.native.published,before)
        self.assertEqual(root.state,b'published')

    def test_private_native_record_changes_are_detected_before_entry(self):
        root=self.root();before=root.native.published
        prepared=root.prepare(error_frame('falha'))
        prepared._record.publish=1 # diagnostic mutation of a private record
        with self.assertRaisesRegex(ValueError,'seal'):
            root.finish(prepared,scope=1,ceiling=100,deadline_ns=101)
        self.assertIsNone(root._pending)
        self.assertEqual(root.native.published,before)
        self.assertIsNone(root.native.completed)

    def test_result_allocation_failure_abandons_pending_and_allows_close(self):
        root=self.root()
        prepared=root.prepare(b'ready',with_limit=True)
        with patch.object(commit,'NativeCommitResult',side_effect=MemoryError('before C')):
            with self.assertRaises(MemoryError):
                root.finish_or_limit(prepared,scope=1,ceiling=100,deadline_ns=101,instrument_deadline_ns=200)
        self.assertIsNone(root._pending)
        self.assertIsNone(root.native.completed)
        root.close()
        self.assertEqual(root._records,{})
        self.assertTrue(root.stack.closed)
        self.assertIsNone(root.library)

    def test_resource_conversion_failure_abandons_pending(self):
        root=self.root()
        prepared=root.prepare(b'ready',with_limit=True)
        with self.assertRaises(ValueError):
            root.finish_or_limit(prepared,scope=1,ceiling=100,deadline_ns=101,instrument_deadline_ns=-1)
        self.assertIsNone(root._pending)
        another=root.prepare(b'other')
        self.assertEqual(root.finish(another,scope=1,ceiling=100,deadline_ns=101),b'other')

    def test_missing_limit_alternative_abandons_pending_before_entry(self):
        root=self.root();prepared=root.prepare(b'candidate')
        with self.assertRaisesRegex(ValueError,'before entry'):
            root.finish_or_limit(prepared,scope=1,ceiling=100,deadline_ns=101,instrument_deadline_ns=200)
        self.assertIsNone(root._pending)
        self.assertIsNone(root.native.completed)
        another=root.prepare(b'next')
        self.assertEqual(root.finish(another,scope=1,ceiling=100,deadline_ns=101),b'next')

    def test_close_releases_internal_records_and_is_terminal(self):
        root=self.root()
        prepared=root.prepare(b'ready',state=b'new',with_limit=True)
        root.finish_or_limit(prepared,scope=1,ceiling=100,deadline_ns=101,instrument_deadline_ns=200)
        reference=weakref.ref(prepared)
        del prepared
        root.close();root.close();gc.collect()
        self.assertIsNone(reference())
        self.assertEqual(root._records,{})
        self.assertIsNone(root.native.published)
        self.assertIsNone(root.native.completed)
        with self.assertRaisesRegex(RuntimeError,'closed'):_=root.state
        with self.assertRaisesRegex(RuntimeError,'closed'):root.prepare(b'next')

    def test_close_can_abandon_a_record_not_entered_into_c(self):
        root=self.root()
        prepared=root.prepare(b'not submitted',state=b'not published',with_limit=True)
        reference=weakref.ref(prepared);del prepared
        root.close();gc.collect()
        self.assertIsNone(reference())
        self.assertIsNone(root.library)

    def test_database_retains_root_until_stack_and_library_cleanup_complete(self):
        root=self.root()
        db=controller.Database.__new__(controller.Database)
        db.modules={}
        db.directory=tempfile.TemporaryDirectory(prefix='jaydb-stack-retry-')
        self.addCleanup(db.directory.cleanup)
        # The buffer export is a local API diagnostic, not client input.
        db._published_root=root
        held=memoryview(root.stack)
        try:
            with self.assertRaises(BufferError):db.close()
            self.assertIs(db._published_root,root)
            self.assertIsNone(root.library)
            self.assertFalse(root.cleanup_complete)
        finally:held.release()
        db.close()
        self.assertTrue(root.cleanup_complete)
        self.assertTrue(root.stack.closed)
        self.assertIsNone(db._published_root)

    def test_completion_exposes_readonly_record_and_owner(self):
        db,root,counter,completion,compile_request,paths,events,response=fixtures.CompletionTests.setup_request(self)
        for name in ('prepared','root','monitor'):
            with self.subTest(name=name):
                with self.assertRaises(AttributeError):setattr(completion,name,None)

    def test_postspawn_collection_failure_kills_and_reaps_helper(self):
        original=ProcessOwner.start
        created=[]
        def spawn(owner):
            result=original(owner);created.append((owner,owner.pid,owner.stdout,owner.stderr));return result
        lines,base=inspect.getsourcelines(controller.helper)
        target=base+next(i for i,line in enumerate(lines) if 'collected = {' in line)
        def trace(frame,event,arg):
            if event=='line' and frame.f_code is controller.helper.__code__ and frame.f_lineno==target:
                raise MemoryError('postspawn collection')
            return trace
        try:
            with patch.object(ProcessOwner,'start',spawn):
                sys.settrace(trace)
                try:
                    with self.assertRaisesRegex(MemoryError,'postspawn'):
                        controller.helper([sys.executable,'-I','-S','-c','import time;time.sleep(60)'],
                            time.monotonic_ns()+10**10,10**9)
                finally:sys.settrace(None)
            self.assertEqual(len(created),1)
            p,pid,out,err=created[0]
            self.assertEqual(p.returncode,-signal.SIGKILL)
            self.assertFalse(Path(f'/proc/{pid}').exists())
            self.assertTrue(out.closed and err.closed)
        finally:
            for p,*_ in created:
                p.close()

    def test_bound_preentry_failure_does_not_prevent_database_close(self):
        db,root,counter,completion,compile_request,paths,events,response=fixtures.CompletionTests.setup_request(self)
        db.bind_request_completion(completion,instrument_deadline_ns=10**30)
        reference=None
        with patch('tools.service.controller.build',side_effect=compile_request), \
                patch.object(commit,'NativeCommitResult',side_effect=MemoryError('before C')):
            with self.assertRaises(MemoryError):db.request(b'body')
        reference=weakref.ref(completion.prepared)
        del completion
        db.modules={}
        db.close();gc.collect()
        self.assertIsNone(root.library)
        self.assertIsNone(db._last_completion)
        self.assertIsNone(reference())
        with self.assertRaisesRegex(RuntimeError,'closed'):db.request(b'next')

    def test_database_close_attempts_all_owners_after_one_failure(self):
        db,root,counter,completion,compile_request,paths,events,response=fixtures.CompletionTests.setup_request(self)
        db.bind_request_completion(completion,instrument_deadline_ns=10**30)
        calls=[]
        def fail():calls.append('bad');raise OSError('actual close failure')
        db.modules={'bad':SimpleNamespace(close=fail),'good':SimpleNamespace(close=lambda:calls.append('good'))}
        with self.assertRaises(OSError):db.close()
        self.assertEqual(calls,['bad','good'])
        self.assertEqual(set(db.modules),{'bad'})
        self.assertIsNone(root.library)
        self.assertIsNone(db._last_completion)
        with self.assertRaisesRegex(RuntimeError,'closed'):_=db.state
        db.modules['bad'].close=lambda:calls.append('retry')
        db.close()
        self.assertEqual(db.modules,{})

    def test_interrupted_execution_uses_native_original_epoch_for_completion(self):
        db,root,counter,completion,compile_request,paths,events,response=fixtures.CompletionTests.setup_request(self)
        module,limits=compile_request(None,Path('unused'),None,None,memory_window=completion.monitor)
        events.clear()
        module.last_accounted_receipt=SimpleNamespace(timing_flags=3,decision_deadline_ns=100)
        def interrupted(*args,**kwargs):raise controller.NativeFailure(3,0,1)
        module.run_accounted=interrupted
        db.bind_request_completion(completion,instrument_deadline_ns=10**30)
        with patch('tools.service.controller.build',return_value=(module,limits)):
            self.assertEqual(db.request(b'body'),error_frame('limite'))
        self.assertEqual(root.last_result.status,2) # own clock100 == ORIGINALepoch100
        self.assertEqual(root.native.completed,completion.prepared.limited.address)
        self.assertEqual(db.state,b'published')

if __name__=='__main__':unittest.main()
