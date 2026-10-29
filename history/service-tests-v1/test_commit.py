"""Publication boundary tests. Synthetic coverage is confined to the fixture;
the real observer must refuse publication while it reports INCOMPLETE.
"""
from __future__ import annotations
import ctypes as C
from dataclasses import FrozenInstanceError
import errno
import json
import signal
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from tools.service.build_commit import build
from tools.service.commit import Root, CommitFailure, LIMIT_FRAME


class CommitTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory(prefix='jaydb2-commit-test-')
        cls.output = Path(cls.directory.name)
        cls.production = cls.output/'production.so'
        cls.fixture_path = cls.output/'fixture.so'
        cls.report = build(cls.production)
        build(cls.fixture_path,test_fixture=ROOT/'tests/service/commit_fixture.c')

    @classmethod
    def tearDownClass(cls):
        cls.directory.cleanup()

    def root(self):
        root = Root(self.fixture_path,b'published',_test_fixture=True)
        root.library.jaydb_commit_fixture.argtypes=[C.c_uint64]*8
        root.library.jaydb_commit_fixture.restype=None
        root.library.jaydb_commit_fixture_counts.argtypes=[C.c_uint]
        root.library.jaydb_commit_fixture_counts.restype=C.c_uint64
        self.addCleanup(root.close)
        return root

    def fixture(self,root,*,flags=9,scope=1,current=100,peak=100,now=100,
                begin_error=0,close_error=0,release_error=0):
        root.library.jaydb_commit_fixture(flags,scope,current,peak,now,
                                           begin_error,close_error,release_error)

    def test_production_critical_has_no_external_call_and_no_test_fixture(self):
        self.assertTrue(self.report['criticalIsLeaf'])
        self.assertTrue(self.report['criticalFixedLoopsAndRawSyscallsOnly'])
        self.assertFalse(self.report['testFixture'])
        symbols=subprocess.check_output(['nm','-D',str(self.production)],text=True)
        self.assertNotIn('fixture',symbols)
        self.assertNotIn(' U ',symbols)
        with self.assertRaisesRegex(ValueError,'unit-test fixture'):
            Root(self.fixture_path,b'published')

    def test_fixture_cannot_be_enabled_by_editing_only_its_report(self):
        artifact=self.output/'renamed-fixture.so'
        artifact.write_bytes(self.fixture_path.read_bytes())
        report=json.loads(self.fixture_path.with_suffix('.so.json').read_text())
        report['testFixture']=False
        report['criticalFixedLoopsAndRawSyscallsOnly']=True
        artifact.with_suffix('.so.json').write_text(json.dumps(report))
        with self.assertRaisesRegex(ValueError,'loaded|Loaded'):
            Root(artifact,b'published')

    def test_rebuild_preserves_mapped_root_and_loaded_identity_rejects_cached_old_dso(self):
        artifact=self.output/'rebuild.so'
        source=self.output/'rebuild-fixture.c'
        original=(ROOT/'tests/service/commit_fixture.c').read_text().replace(
            '"../../tools/service/commit.h"','"'+str(ROOT/'tools/service/commit.h')+'"')
        source.write_text(original)
        first=build(artifact,test_fixture=source)
        old=Root(artifact,b'old state',_test_fixture=True)
        self.addCleanup(old.close)
        old.library.jaydb_commit_fixture.argtypes=[C.c_uint64]*8
        old.library.jaydb_commit_fixture(9,1,40,100,100,0,0,0)
        source.write_text(original+'\n/* A distinct build, same public ABI. */\n')
        second=build(artifact,test_fixture=source)
        self.assertNotEqual(first['buildIdentitySha256'],second['buildIdentitySha256'])
        self.assertNotEqual(first['moduleSha256'],second['moduleSha256'])
        # dlopen caches by loaded path: the new disk hash alone cannot select
        # the mapping that a second Root receives while the first owns it.
        with self.assertRaisesRegex(ValueError,'loaded|Loaded'):
            Root(artifact,b'other state',_test_fixture=True)
        prepared=old.prepare(b'old module still works',state=b'committed')
        self.assertEqual(old.finish(prepared,scope=1,ceiling=100,deadline_ns=101),
                         b'old module still works')
        old.close()
        current=Root(artifact,b'new build',_test_fixture=True)
        self.addCleanup(current.close)
        self.assertEqual(current.state,b'new build')

    def test_memory_equality_allows_single_publication(self):
        root=self.root()
        self.fixture(root,current=40,peak=100)
        prepared=root.prepare(b'ready response',state=b'new state')
        self.assertEqual(root.finish(prepared,scope=1,ceiling=100,deadline_ns=101),b'ready response')
        self.assertIs(root.state,prepared.state)
        self.assertEqual(root.native.published,prepared.address)
        self.assertEqual(root.native.completed,prepared.address)
        self.assertEqual(root.last_result.window.peak_sequence.integer(),20)

    def test_non_success_completes_without_a_publication_store(self):
        root=self.root()
        before=root.native.published
        self.fixture(root)
        prepared=root.prepare(b'prepared recusa')
        self.assertEqual(root.finish(prepared,scope=1,ceiling=100,deadline_ns=101),b'prepared recusa')
        self.assertEqual(root.native.published,before)
        self.assertEqual(root.state,b'published')
        self.assertEqual(root.native.completed,prepared.address)

    def test_actual_local_peak_excess_refuses_even_after_current_falls(self):
        root=self.root()
        before=root.native.published
        self.fixture(root,current=40,peak=101)
        prepared=root.prepare(b'response',state=b'new')
        with self.assertRaises(CommitFailure) as failure:
            root.finish(prepared,scope=1,ceiling=100,deadline_ns=101)
        self.assertEqual(failure.exception.result.status,1)
        self.assertEqual(root.native.published,before)
        self.assertFalse(root.native.completed)
        self.assertEqual(root.library.jaydb_commit_fixture_counts(2),1)

    def test_deadline_equality_refuses_before_pointer_store(self):
        root=self.root()
        self.fixture(root,now=100)
        prepared=root.prepare(b'response',state=b'new')
        with self.assertRaises(CommitFailure) as failure:
            root.finish(prepared,scope=1,ceiling=100,deadline_ns=100)
        self.assertEqual(failure.exception.result.status,2)
        self.assertEqual(root.state,b'published')

    def test_incomplete_or_dead_owner_cannot_authorize_publication(self):
        root=self.root()
        for flags in (11,13,1):
            self.fixture(root,flags=flags)
            prepared=root.prepare(b'response',state=b'new')
            with self.assertRaises(CommitFailure) as failure:
                root.finish(prepared,scope=1,ceiling=10**500,deadline_ns=10**500)
            self.assertEqual(failure.exception.result.status,3)
            self.assertEqual(root.state,b'published')

    def test_scope_mismatch_and_marker_error_do_not_complete(self):
        root=self.root()
        for scope,close_error in ((2,0),(1,errno.ETIMEDOUT)):
            self.fixture(root,scope=scope,close_error=close_error)
            prepared=root.prepare(b'response',state=b'new')
            with self.assertRaises(CommitFailure) as failure:
                root.finish(prepared,scope=1,ceiling=100,deadline_ns=101)
            self.assertEqual(failure.exception.result.status,4)
            self.assertEqual(root.state,b'published')
            self.assertEqual(root.library.jaydb_commit_fixture_counts(2),1)

    def test_cancelled_marker_uses_own_clock_before_claiming_timeout(self):
        root=self.root()
        for now,expected in ((100,2),(99,4)):
            self.fixture(root,now=now,close_error=errno.ETIMEDOUT)
            prepared=root.prepare(b'response',state=b'new')
            with self.assertRaises(CommitFailure) as failure:
                root.finish(prepared,scope=1,ceiling=100,deadline_ns=100)
            self.assertEqual(failure.exception.result.status,expected)
            self.assertEqual(root.state,b'published')
            self.assertEqual(root.library.jaydb_commit_fixture_counts(2),1)

    def test_ffi_exception_and_release_error_after_commit_preserve_response(self):
        root=self.root()
        self.fixture(root,release_error=errno.EIO)
        prepared=root.prepare(b'already prepared',state=b'committed')
        real=root.library.jaydb_commit_finish
        def interrupted_return(*args):
            real(*args)
            raise RuntimeError('exception before ctypes return assignment')
        root.library.jaydb_commit_finish=interrupted_return
        self.assertEqual(root.finish(prepared,scope=1,ceiling=100,deadline_ns=101),b'already prepared')
        self.assertEqual(root.state,b'committed')
        self.assertEqual(root.last_result.release_error,errno.EIO)
        # Preparation of a later refusal retains the committed state object.
        root.library.jaydb_commit_finish=real
        self.fixture(root)
        refusal=root.prepare(b'recusa')
        self.assertEqual(root.finish(refusal,scope=1,ceiling=100,deadline_ns=101),b'recusa')
        self.assertEqual(root.state,b'committed')
        self.assertEqual(root.native.published,prepared.address)

    def test_real_observer_incomplete_refuses_and_releases_hold(self):
        # This real ptrace test is deliberately a refusal test. Synthetic
        # complete snapshots above cannot certify the real measurement.
        from tools.accounting.build import build as accounting_build
        library,tracer=accounting_build(self.output/'accounting')
        program=self.output/'real_probe.py'
        program.write_text('''import sys,time,json
sys.path.insert(0,sys.argv[1])
from tools.accounting.client import Library
from tools.service.commit import Root,CommitFailure
lib=Library(sys.argv[2]);root=Root(sys.argv[3],b"published")
w=lib.window_begin();p=root.prepare(b"response",state=b"expired candidate")
try:
  root.finish(p,scope=w.scope_id,ceiling=10**100,deadline_ns=1)
  raise AssertionError("expired deadline authorized publication")
except CommitFailure as e:
  assert e.result.status==2,(e.result.status,e.result.instrument_error)
  assert e.result.checked_ns.integer()>=1
assert root.state==b"published"
assert lib.window_barrier().require_scope(w.scope_id).active
lib.window_end()
w=lib.window_begin();p=root.prepare(b"response",state=b"new")
try:
  root.finish(p,scope=w.scope_id,ceiling=10**100,deadline_ns=time.monotonic_ns()+10**10)
  raise AssertionError("incomplete observer authorized publication")
except CommitFailure as e:
  assert e.result.status==3,(e.result.status,e.result.instrument_error)
assert root.state==b"published"
assert root.native.completed is None
scope=lib.window_begin();p=root.prepare(b"candidate",state=b"new",with_limit=True)
try:
  root.finish_or_limit(p,scope=scope.scope_id,ceiling=1,
    deadline_ns=time.monotonic_ns()+10**10,instrument_deadline_ns=time.monotonic_ns()+10**10)
  raise AssertionError("incomplete excess completed a fixed resource error")
except CommitFailure as e:
  assert e.result.status==3,(e.result.status,e.result.instrument_error)
assert root.state==b"published" and root.native.completed is None
next_scope=lib.window_begin();assert next_scope.scope_id>w.scope_id
lib.window_end();root.close()
print(json.dumps({"refusedIncomplete":True,"releasedHold":True,"expiredMarkerKeptScope":True}))
''')
        report=self.output/'real.jsonl'
        result=subprocess.run([str(tracer),'--report',str(report),'--',sys.executable,'-B',
            str(program),str(ROOT),str(library),str(self.production)],capture_output=True,text=True,timeout=30)
        self.assertEqual(result.returncode,0,result.stderr+result.stdout)
        self.assertEqual(json.loads(result.stdout),{'refusedIncomplete':True,'releasedHold':True,'expiredMarkerKeptScope':True})

    def test_actual_signal_dispatched_after_commit_retains_prepared_response(self):
        root=self.root()
        self.fixture(root)
        root.library.jaydb_commit_fixture_signal.argtypes=[C.c_int]
        root.library.jaydb_commit_fixture_signal.restype=None
        root.library.jaydb_commit_fixture_signal(signal.SIGALRM)
        prepared=root.prepare(b'prepared',state=b'new state')
        previous=signal.signal(signal.SIGALRM,lambda *args: (_ for _ in ()).throw(RuntimeError('actual signal after commit')))
        try:
            self.assertEqual(root.finish(prepared,scope=1,ceiling=100,deadline_ns=101),b'prepared')
            self.assertEqual(root.state,b'new state')
        finally:
            signal.signal(signal.SIGALRM,previous)

    def test_fixed_limit_frame_is_exact_and_has_absent_value(self):
        from tools.client import frame,unframe
        expected={'status':'limite','valor':None}
        self.assertEqual(LIMIT_FRAME,frame(expected))
        self.assertEqual(unframe(LIMIT_FRAME),expected)

    def test_resolve_excess_completes_fixed_error_without_publishing_candidate(self):
        root=self.root()
        before=root.native.published
        self.fixture(root,current=40,peak=101)
        prepared=root.prepare(b'candidate response',state=b'candidate state',with_limit=True)
        self.assertEqual(root.finish_or_limit(prepared,scope=1,ceiling=100,
            deadline_ns=101,instrument_deadline_ns=200),LIMIT_FRAME)
        self.assertEqual(root.native.published,before)
        self.assertEqual(root.state,b'published')
        self.assertEqual(root.native.completed,prepared.limited.address)
        self.assertEqual(root.last_result.status,1)
        self.assertEqual(root.last_result.window.peak_sequence.integer(),20)
        self.assertEqual(root.library.jaydb_commit_fixture_counts(4),1)
        self.assertEqual(root.library.jaydb_commit_fixture_counts(2),1)

    def test_resolve_equality_uses_candidate_and_never_completes_fallback(self):
        root=self.root()
        self.fixture(root,current=40,peak=100,now=100)
        prepared=root.prepare(b'ready',state=b'new',with_limit=True)
        self.assertEqual(root.finish_or_limit(prepared,scope=1,ceiling=100,
            deadline_ns=101,instrument_deadline_ns=200),b'ready')
        self.assertEqual(root.state,b'new')
        self.assertEqual(root.native.completed,prepared.address)
        self.assertEqual(root.last_result.status,0)

    def test_resolve_keeps_original_decision_deadline_during_cleanup(self):
        root=self.root()
        self.fixture(root,now=100)
        prepared=root.prepare(b'too late',state=b'candidate',with_limit=True)
        self.assertEqual(root.finish_or_limit(prepared,scope=1,ceiling=100,
            deadline_ns=100,instrument_deadline_ns=200),LIMIT_FRAME)
        self.assertEqual(root.state,b'published')
        self.assertEqual(root.native.completed,prepared.limited.address)
        self.assertEqual(root.last_result.status,2)
        self.assertEqual(root.last_result.checked_ns.integer(),100)

    def test_resolve_does_not_use_incomplete_measurement_to_complete_limit(self):
        root=self.root()
        self.fixture(root,flags=11,current=101,peak=101)
        prepared=root.prepare(b'candidate',state=b'new',with_limit=True)
        with self.assertRaises(CommitFailure) as failure:
            root.finish_or_limit(prepared,scope=1,ceiling=100,
                deadline_ns=101,instrument_deadline_ns=200)
        self.assertEqual(failure.exception.result.status,3)
        self.assertFalse(root.native.completed)
        self.assertEqual(root.state,b'published')

    def test_invalid_snapshot_abi_timestamp_or_peak_flags_cannot_complete(self):
        root=self.root()
        root.library.jaydb_commit_fixture_invalid.argtypes=[C.c_uint]
        before=root.native.published
        for which in range(4):
            with self.subTest(which=which):
                self.fixture(root)
                root.library.jaydb_commit_fixture_invalid(which)
                prepared=root.prepare(b'response',state=b'new',with_limit=True)
                with self.assertRaises(CommitFailure):
                    root.finish_or_limit(prepared,scope=1,ceiling=100,deadline_ns=101,
                                         instrument_deadline_ns=200)
                self.assertEqual(root.native.published,before)
                self.assertFalse(root.native.completed)
        self.assertEqual(root.state,b'published')

    def test_resolve_requires_prepared_nonpublishing_fallback_for_old_state(self):
        root=self.root()
        self.fixture(root)
        prepared=root.prepare(b'ready')
        with self.assertRaisesRegex(ValueError,'must be prepared'):
            root.finish_or_limit(prepared,scope=1,ceiling=100,
                deadline_ns=101,instrument_deadline_ns=200)
        self.assertIsNone(root._pending)
        prepared=root.prepare(b'ready')
        self.assertEqual(root.finish(prepared,scope=1,ceiling=100,deadline_ns=101),b'ready')
        prepared=root.prepare(b'candidate',state=b'new',with_limit=True)
        with self.assertRaises(FrozenInstanceError):
            prepared.limited.native.publish=1
        # A diagnostic private-record change is also caught by the seal before
        # the C boundary. Public inspection cannot mutate that record.
        prepared.limited._record.publish=1
        with self.assertRaisesRegex(ValueError,'seal'):
            root.finish_or_limit(prepared,scope=1,ceiling=100,
                deadline_ns=101,instrument_deadline_ns=200)
        self.assertEqual(root.state,b'published')

    def test_ffi_exception_after_selected_limit_keeps_error_and_old_state(self):
        root=self.root()
        before=root.native.published
        self.fixture(root,current=40,peak=101,release_error=errno.EIO)
        prepared=root.prepare(b'candidate',state=b'new',with_limit=True)
        real=root.library.jaydb_commit_resolve
        def interrupted_return(*args):
            real(*args)
            raise RuntimeError('exception after durable error completion')
        root.library.jaydb_commit_resolve=interrupted_return
        self.assertEqual(root.finish_or_limit(prepared,scope=1,ceiling=100,
            deadline_ns=101,instrument_deadline_ns=200),LIMIT_FRAME)
        self.assertEqual(root.native.published,before)

        self.assertEqual(root.native.completed,prepared.limited.address)
        self.assertEqual(root.last_result.release_error,errno.EIO)
        root.library.jaydb_commit_resolve=real
        self.fixture(root)
        next_call=root.prepare(b'next')
        self.assertEqual(root.finish(next_call,scope=1,ceiling=100,deadline_ns=101),b'next')
        self.assertEqual(root.native.published,before)

    def test_actual_signal_after_selecting_limit_preserves_completed_error(self):
        root=self.root()
        self.fixture(root,now=100)
        root.library.jaydb_commit_fixture_signal.argtypes=[C.c_int]
        root.library.jaydb_commit_fixture_signal.restype=None
        root.library.jaydb_commit_fixture_signal(signal.SIGALRM)
        prepared=root.prepare(b'candidate',state=b'new',with_limit=True)
        previous=signal.signal(signal.SIGALRM,lambda *args: (_ for _ in ()).throw(RuntimeError('signal after error completion')))
        try:
            self.assertEqual(root.finish_or_limit(prepared,scope=1,ceiling=100,
                deadline_ns=100,instrument_deadline_ns=200),LIMIT_FRAME)
            self.assertEqual(root.state,b'published')
            self.assertEqual(root.native.completed,prepared.limited.address)
        finally:
            signal.signal(signal.SIGALRM,previous)


if __name__=='__main__':
    unittest.main()
