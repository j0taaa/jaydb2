"""Controller/C-root integration with explicit numerical coverage fixtures.

No fixture is a MedicaoReal. Actual observer coverage is still INCOMPLETE.
"""
import ctypes as C
from pathlib import Path
import sys
import tempfile
import time
from types import SimpleNamespace
import unittest
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from tools.accounting.client import Snapshot,WindowSnapshot,IncompleteCoverage
from tools.client import frame,unframe
from tools.service.build_commit import build
from tools.service.commit import Root,CommitFailure
from tools.service.completion import RequestCompletion
from tools.service.controller import Database,IncompleteIntegration,packet,error_frame


class CompletionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp=tempfile.TemporaryDirectory(prefix='jaydb2-request-completion-')
        cls.library=Path(cls.temp.name)/'fixture.so'
        build(cls.library,test_fixture=ROOT/'tests/service/commit_fixture.c')

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def setup_request(self, *, peak=100, flags=9, cleanup_error=False):
        root=Root(self.library,b'published',_test_fixture=True)
        self.addCleanup(root.close)
        root.library.jaydb_commit_fixture.argtypes=[C.c_uint64]*8
        root.library.jaydb_commit_fixture(9,1,40,peak,100,0,0,0)
        # Both the native boundary and the shared-reader observations are
        # synthetic fixtures, using the same scope and local peak.
        snapshot=Snapshot(20,40,1000,200,30,3,flags,flags)
        window=WindowSnapshot(snapshot,1,1,10,100,0,0,peak,170,17,flags)
        counter=SimpleNamespace(window_read=lambda:window)
        db=Database.__new__(Database)
        db.state=b'published'
        db.limits={k:10**9 for k in ('enquadramento','autenticacao','verificacao',
                                    'execucao','preparacao')}
        db.limits.update(memoria=100,estado=1000,resposta=1000)
        db.environment=db.toolchain=db.runtime=None
        directory=tempfile.TemporaryDirectory(prefix='jaydb2-request-completion-db-')
        self.addCleanup(directory.cleanup)
        db.directory=directory
        events=[]
        metadata=packet(b'code',packet(b'proof',packet(b'instance',b'bindings')))
        def decoded(data,**options):
            self.assertIs(options['accounting'].counter,counter)
            events.append('decode')
            return b'\1'
        def authenticated(data,**options):
            self.assertIs(options['accounting'].counter,counter)
            events.append('authenticate')
            return b'\1'+metadata
        db.modules={'decode':SimpleNamespace(run_accounted=decoded),
                    'authenticate':SimpleNamespace(run_accounted=authenticated)}
        response=frame({'status':'sucesso','valor':123})
        def execute(data,**options):
            self.assertIs(options['accounting'].counter,counter)
            self.assertIs(options['accounting'],db._active_request_completion.monitor)
            events.append('execute')
            return b'\1'+packet(b'new state',response)
        def close():
            events.append('close')
            if cleanup_error:
                raise OSError('actual cleanup failed')
        module=SimpleNamespace(run_accounted=execute,close=close,
                               preparation_deadline=time.monotonic_ns()+10**9)
        staged=[]
        def compile_request(environment,path,purpose,toolchain,**options):
            staged.append(path)
            self.assertIs(options['memory_window'].counter,counter)
            events.append('build')
            return module,db.limits
        completion=RequestCompletion(root,counter,1,100) if not flags&2 else None
        return db,root,counter,completion,compile_request,staged,events,response

    def test_success_uses_c_root_after_cleanup_and_cannot_publish_in_python(self):
        db,root,counter,completion,compile_request,paths,events,response=self.setup_request()
        db.bind_request_completion(completion,instrument_deadline_ns=10**30)
        finish=completion.finish
        def after_cleanup(*args,**kwargs):
            self.assertEqual(events,['decode','authenticate','build','execute','close'])
            self.assertTrue(paths and all(not path.exists() for path in paths))
            return finish(*args,**kwargs)
        with patch('tools.service.controller.build',side_effect=compile_request), \
                patch.object(completion,'finish',side_effect=after_cleanup):
            self.assertEqual(db.request(b'body'),response)
        self.assertEqual(db.state,b'new state')
        self.assertEqual(root.native.published,completion.prepared.address)
        self.assertTrue(completion.completed)
        self.assertEqual(completion.response,response)
        with self.assertRaisesRegex(RuntimeError,'Only the retained C root'):
            db.state=b'forged'
        with self.assertRaisesRegex(RuntimeError,'fresh request completion scope'):
            db.request(b'next')

    def test_transient_peak_selects_limit_without_publishing_proposal(self):
        db,root,counter,completion,compile_request,paths,events,response=self.setup_request(peak=101)
        before=root.native.published
        db.bind_request_completion(completion,instrument_deadline_ns=10**30)
        with patch('tools.service.controller.build',side_effect=compile_request):
            actual=db.request(b'body')
        self.assertEqual(unframe(actual),{'status':'limite','valor':None})
        self.assertEqual(db.state,b'published')
        self.assertEqual(root.native.published,before)
        self.assertEqual(root.native.completed,completion.prepared.limited.address)
        self.assertTrue(completion.completed)

    def test_cleanup_error_completes_failure_and_keeps_old_root(self):
        db,root,counter,completion,compile_request,paths,events,response=self.setup_request(cleanup_error=True)
        before=root.native.published
        db.bind_request_completion(completion,instrument_deadline_ns=10**30)
        with patch('tools.service.controller.build',side_effect=compile_request):
            actual=db.request(b'body')
        self.assertEqual(unframe(actual),{'status':'falha','valor':None})
        self.assertEqual(db.last_failure['code'],'OSError')
        self.assertEqual(root.native.published,before)
        self.assertTrue(completion.completed)

    def test_return_exception_after_publication_preserves_selected_response(self):
        db,root,counter,completion,compile_request,paths,events,response=self.setup_request()
        db.bind_request_completion(completion,instrument_deadline_ns=10**30)
        native=root.library.jaydb_commit_resolve
        def return_exception(*args):
            native(*args)
            raise RuntimeError('pending handler at FFI return')
        with patch('tools.service.controller.build',side_effect=compile_request), \
                patch.object(root.library,'jaydb_commit_resolve',side_effect=return_exception):
            self.assertEqual(db.request(b'body'),response)
        self.assertEqual(db.state,b'new state')
        self.assertEqual(completion.response,response)
        self.assertIsNone(db.last_failure)

    def test_completion_instrument_error_is_not_mapped_to_another_response(self):
        db,root,counter,completion,compile_request,paths,events,response=self.setup_request()
        db.bind_request_completion(completion,instrument_deadline_ns=10**30)
        root.library.jaydb_commit_fixture(9,1,40,100,100,22,0,0)
        with patch('tools.service.controller.build',side_effect=compile_request):
            with self.assertRaises(CommitFailure):
                db.request(b'body')
        self.assertEqual(db.state,b'published')
        self.assertFalse(completion.completed)
        with self.assertRaisesRegex(RuntimeError,'no durable completed response'):
            _=completion.response

    def test_incomplete_observation_and_old_native_path_cannot_bind(self):
        db,root,counter,completion,compile_request,paths,events,response=self.setup_request(flags=3)
        with self.assertRaises(IncompleteCoverage):
            RequestCompletion(root,counter,1,100)
        self.assertFalse(root.native.completed)
        db,root,counter,completion,compile_request,paths,events,response=self.setup_request()
        db.modules['decode']=SimpleNamespace(run=lambda *args,**kwargs:b'\1')
        with self.assertRaises(IncompleteIntegration):
            db.bind_request_completion(completion,instrument_deadline_ns=10**30)
        self.assertFalse(root.native.completed)
        self.assertIsNone(getattr(db,'_published_root',None))

    def test_completion_requires_same_initial_root_and_public_ceiling(self):
        db,root,counter,completion,compile_request,paths,events,response=self.setup_request()
        db.state=b'other state'
        with self.assertRaises(ValueError):
            db.bind_request_completion(completion,instrument_deadline_ns=10**30)
        db.state=b'published'
        db.limits['memoria']=101
        with self.assertRaises(ValueError):
            db.bind_request_completion(completion,instrument_deadline_ns=10**30)


if __name__=='__main__':
    unittest.main(verbosity=2)
