"""Private field ABI. Positive observations are fixtures, never MedicaoReal.
Real ptrace cases must reject INCOMPLETE; no public service success is tested.
"""
import ctypes as C
import errno
import importlib.util
import json
import mmap
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(Path(__file__).parent))
from test_constructor import U128,Snapshot
U64=C.c_uint64
SPEC=importlib.util.spec_from_file_location('field_build',ROOT/'tools/native/build_field.py')
BUILD=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(BUILD)

class Window(C.Structure):
    _fields_=[('abi',U64),('state',U64),('error',U64),('snapshot',Snapshot),
        *[(name,U128) for name in ['scope_id','begin_sequence','begin_monotonic_ns',
          'end_sequence','end_monotonic_ns','peak','peak_monotonic_ns','peak_sequence']],('peak_flags',U64)]
class Owner(C.Structure):
    _fields_=[('address',C.c_void_p),('capacity',U64)]
class Span(C.Structure):
    _fields_=[('owner',U64),('offset',U64),('source',C.c_void_p),('bytes',U64)]
class Wire(C.Structure):
    _fields_=[('bytes',C.c_void_p),*[(n,U64) for n in ['size','limit','position','name']],('pending_minimum',U128)]
class Request(C.Structure):
    _fields_=[('abi',U64),('constructor_id',U64),('site_id',U64),('wire',Wire),
        ('scope',U128),('ceiling',U128),('deadline',U128),('owners',C.POINTER(Owner)),
        ('owner_count',U64),('spans',C.POINTER(Span)),('span_count',U64)]
class Result(C.Structure):
    _fields_=[*[(n,U64) for n in ['status','length_checked','construction_started','constructed',
        'instrument_error','release_error','clock_error','backing_error','position','quantity',
        'tag','acquired_bytes','stores_completed']],('window',Window),('checked_ns',U128)]
class Fixture(C.Structure):
    _fields_=[*[(n,U64) for n in ['flags','current','peak','global_peak','now','scope','peak_flags',
        'fail_op','error','map_error','release_error','clock_error','invalid','signal','holds',
        'finals','releases','maps','mapped_bytes','early_stores','closed']],('deadlines',U64*3),('maps_at_final',U64),('fail_map_index',U64),('clock_calls',U64),('advance_at',U64),('advance_ns',U64)]

def var(tag,n,payload=b''):return bytes([tag])+n.to_bytes(8,'big')+payload

class Bridge:
    def __init__(self,path,fixture=False):
        self.lib=C.CDLL(str(path))
        self.lib.jaydb_field_stack_bytes_v2.restype=U64
        self.size=self.lib.jaydb_field_stack_bytes_v2()
        self.stack=mmap.mmap(-1,self.size);self.stack[:]=bytes(self.size)
        self.view=C.c_char.from_buffer(self.stack)
        self.lib.jaydb_field_construct_v2.argtypes=[C.POINTER(Request),C.c_void_p,U64,C.POINTER(Result)]
        self.lib.jaydb_field_construct_v2.restype=U64
        if fixture:
            self.lib.jaydb_field_fixture.restype=C.POINTER(Fixture)
            self.lib.jaydb_field_watch.argtypes=[C.c_void_p,U64]
            self.f=self.lib.jaydb_field_fixture().contents
    def call(self,wire=var(4,3,b'abc'),data=b'prepared representation',*,new=False,ceiling=100,
             deadline=101,pending=0,limit=None,position=0,name=False,count=1,owner=None,scope=7):
        wirebuf=C.create_string_buffer(wire);source=C.create_string_buffer(data)
        dest=(C.c_ubyte*len(data))(*([0xa5]*len(data)))
        if owner is None:owner=Owner(None,0) if new else Owner(C.addressof(dest),len(data))
        owners=(Owner*1)(owner)
        spans=(Span*count)(*(Span(0,i,C.addressof(source)+i,1) for i in range(count))) if count>1 else (Span*1)(Span(0,0,C.addressof(source),len(data)))
        if hasattr(self,'f') and not new:self.lib.jaydb_field_watch(dest,len(data))
        q=Request(2,70000,90000,Wire(C.addressof(wirebuf),len(wire),len(wire) if limit is None else limit,
            position,name,U128.natural(pending)),U128.natural(scope),U128.natural(ceiling),U128.natural(deadline),owners,1,spans,count)
        r=Result()
        status=self.lib.jaydb_field_construct_v2(C.byref(q),C.addressof(self.view),self.size,C.byref(r))
        assert status==r.status
        data_after=C.string_at(owners[0].address,len(data)) if owners[0].address else None
        return r,data_after,owners[0]
    def close(self):
        del self.view;self.stack.close()

class FieldTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp=tempfile.TemporaryDirectory(prefix='jaydb-field-tests-');cls.directory=Path(cls.temp.name)
        cls.production=cls.directory/'production.so';cls.fixture=cls.directory/'fixture.so'
        cls.report=BUILD.build(cls.production)
        BUILD.build(cls.fixture,test_fixture=ROOT/'tests/native/field_fixture.c')
        cls.libc=C.CDLL(None);cls.libc.munmap.argtypes=[C.c_void_p,C.c_size_t]
    @classmethod
    def tearDownClass(cls):cls.temp.cleanup()
    def bridge(self,production=False):
        b=Bridge(self.production if production else self.fixture,not production)
        self.addCleanup(b.close);return b
    def release(self,o):
        self.assertTrue(o.address);self.addCleanup(self.libc.munmap,o.address,o.capacity)
    def test_final_production_is_leaf_and_has_no_fixture_symbols(self):
        self.assertTrue(self.report['criticalIsLeaf']);self.assertFalse(self.report['testFixture'])
        self.assertEqual((C.sizeof(Snapshot),C.sizeof(Window)),(120,280))
        symbols=subprocess.check_output(['nm','-D',str(self.production)],text=True)
        self.assertNotIn(' U ',symbols);self.assertNotIn('test_',symbols)
        self.assertGreaterEqual(self.report['stackBytes'],self.report['criticalFrameBytes']+23)
    def test_synthetic_equality_local_peak_ignores_previous_global_peak(self):
        b=self.bridge();r,data,o=b.call()
        self.assertEqual((r.status,r.length_checked,r.construction_started,r.constructed),(0,1,1,1))
        self.assertEqual(data,b'prepared representation')
        self.assertEqual((r.quantity,r.tag,r.window.state),(3,4,1))
        self.assertEqual((b.f.maps,b.f.finals,b.f.releases,b.f.early_stores,b.f.closed),(0,1,1,0,0))
        self.assertEqual(list(b.f.deadlines)[:2],[101,101])
    def test_synthetic_acquisition_is_real_necessary_and_before_final(self):
        b=self.bridge();r,data,o=b.call(new=True,data=b'x'*4097)
        self.release(o)
        self.assertEqual((r.status,r.acquired_bytes,o.capacity,b.f.maps,b.f.mapped_bytes),(0,8192,8192,1,8192))
        self.assertEqual(data,b'x'*4097)
        self.assertEqual(b.f.maps_at_final,1)
    def test_suballocation_many_spans_acquires_arena_once_no_arity_cap(self):
        b=self.bridge();data=bytes(i%256 for i in range(513))
        r,after,o=b.call(new=True,data=data,count=513);self.release(o)
        self.assertEqual((r.status,r.stores_completed,b.f.maps,b.f.mapped_bytes),(0,513,1,4096))
        self.assertEqual(after,data)
    def test_synthetic_real_excess_retains_backing_but_does_not_construct(self):
        b=self.bridge();b.f.current=101;b.f.peak=101
        r,data,o=b.call(new=True);self.release(o)
        self.assertEqual((r.status,r.construction_started,r.constructed,r.acquired_bytes),(1,0,0,4096))
        self.assertEqual(data,bytes(len(data)))
    def test_local_window_peak_excess_after_consumption_fell(self):
        b=self.bridge();b.f.current=80;b.f.peak=101
        r,data,o=b.call();self.assertEqual(r.status,1);self.assertEqual(data,b'\xa5'*len(data))
    def test_incomplete_current_or_peak_dead_owner_unheld_never_becomes_memory(self):
        for flags,peak_flags in [(11,1),(13,1),(1,1),(8,1),(9,3),(9,5),(9,0)]:
            with self.subTest(flags=flags,peak_flags=peak_flags):
                b=self.bridge();b.f.flags=flags;b.f.peak_flags=peak_flags
                r,data,o=b.call(ceiling=0)
                self.assertEqual((r.status,r.constructed),(3,0));self.assertEqual(data,b'\xa5'*len(data))
    def test_scope_and_window_provenance_fail_before_any_store(self):
        b=self.bridge()
        for invalid in range(1,7):
            b.f.invalid=invalid;r,data,o=b.call()
            self.assertEqual((r.status,r.instrument_error),(4,errno.EINVAL),invalid)
            self.assertEqual(data,b'\xa5'*len(data))
        b.f.invalid=0;b.f.scope=8;r,_,_=b.call();self.assertEqual(r.status,4)
    def test_header_reads_declared_quantity_not_representation_bytes(self):
        b=self.bridge()
        for wire,n in [(var(4,0),0),(var(5,2,b'\0\0'),2),(var(6,1,b'x'*11),1),
                       (b'\0',0),(b'\1',0),(b'\2',0),(b'\3'+bytes(8),8)]:
            r,_,_=b.call(wire=wire,data=bytes(31));self.assertEqual((r.status,r.quantity),(0,n))
    def test_length_and_pending_minimum_reject_before_backing_or_hold(self):
        for wire,pending,expected in [(var(4,4,b'abc'),0,8),(var(6,2,b'x'*21),0,8),
            (var(5,2,b'\0\0'),1,8),(var(4,1,b'x'),(1<<128)-1,8)]:
            b=self.bridge();r,_,_=b.call(wire=wire,pending=pending,new=True)
            self.assertEqual((r.status,r.length_checked,b.f.maps,b.f.holds),(expected,0,0,0))
    def test_fixed_primitive_extent_does_not_apply_variable_pending_guard(self):
        b=self.bridge()
        for wire,n in [(b'\0',0),(b'\1',0),(b'\2',0),(b'\3'+bytes(8),8)]:
            r,_,_=b.call(wire=wire,pending=2**128-1)
            self.assertEqual((r.status,r.quantity,r.length_checked,r.constructed),(0,n,1,1))
    def test_truncated_and_invalid_tags_names_do_not_acquire(self):
        for wire,name in [(b'\4\0',False),(b'\7',False),(var(4,0),True),
                          (var(4,65,b'x'*65),True),(b'\0',True)]:
            b=self.bridge();r,_,_=b.call(wire=wire,name=name,new=True)
            self.assertEqual((r.status,b.f.maps,b.f.holds),(7,0,0))
    def test_body_shortage_with_larger_limit_is_input_not_memory(self):
        b=self.bridge();r,_,_=b.call(wire=var(4,5,b'ab'),limit=100,new=True)
        self.assertEqual((r.status,b.f.maps),(7,0))
    def test_mmap_failure_is_backing_error_never_memory_witness(self):
        b=self.bridge();b.f.map_error=errno.ENOMEM;r,_,o=b.call(new=True,ceiling=0)
        self.assertEqual((r.status,r.backing_error,r.constructed,b.f.releases),(6,errno.ENOMEM,0,1))
        self.assertFalse(o.address)
    def test_deadline_equality_and_timeout_need_own_clock(self):
        b=self.bridge();b.f.now=101;r,data,_=b.call()
        self.assertEqual((r.status,r.constructed),(2,0));self.assertEqual(data,b'\xa5'*len(data))
        for op in [1,5]:
            for now,expected in [(100,4),(101,2)]:
                b=self.bridge();b.f.fail_op=op;b.f.error=errno.ETIMEDOUT;b.f.now=now
                r,_,o=b.call(new=True)
                if o.address:self.release(o)
                self.assertEqual((r.status,r.constructed,r.window.abi,b.f.releases),(expected,0,0,1))
    def test_bad_clock_and_release_failure_do_not_invent_rollback(self):
        b=self.bridge();b.f.clock_error=errno.EIO;r,_,_=b.call()
        self.assertEqual((r.status,r.clock_error,r.constructed),(4,errno.EIO,0))
        b=self.bridge();b.f.release_error=errno.EIO;r,data,_=b.call()
        self.assertEqual((r.status,r.constructed,r.release_error,data),(0,1,errno.EIO,b'prepared representation'))
    def test_signal_handler_runs_after_hold_release_and_sees_durable_completion(self):
        b=self.bridge();events=[]
        previous=signal.signal(signal.SIGUSR1,lambda s,f:events.append(b.f.releases))
        self.addCleanup(signal.signal,signal.SIGUSR1,previous)
        b.f.signal=signal.SIGUSR1;r,data,_=b.call()
        self.assertEqual((r.constructed,events),(1,[1]))
    def test_ffi_signal_exception_cannot_erase_completed_construction(self):
        b=self.bridge();wire=C.create_string_buffer(b'\0');src=C.create_string_buffer(b'actual')
        dest=C.create_string_buffer(b'rawraw');owners=(Owner*1)(Owner(C.addressof(dest),6))
        spans=(Span*1)(Span(0,0,C.addressof(src),6))
        q=Request(2,1,1,Wire(C.addressof(wire),1,1,0,0,U128()),U128.natural(7),
            U128.natural(100),U128.natural(101),owners,1,spans,1)
        r=Result();events=[]
        def interrupted(signum,frame):
            events.append(b.f.releases)
            raise RuntimeError('pending handler at FFI return')
        previous=signal.signal(signal.SIGUSR1,interrupted)
        self.addCleanup(signal.signal,signal.SIGUSR1,previous)
        b.f.signal=signal.SIGUSR1
        with self.assertRaisesRegex(RuntimeError,'pending handler'):
            b.lib.jaydb_field_construct_v2(C.byref(q),C.addressof(b.view),b.size,C.byref(r))
        self.assertEqual((r.status,r.construction_started,r.constructed,events),(0,1,1,[1]))
        self.assertEqual(dest.raw[:6],b'actual')
    def test_u128_ceiling_and_deadline_have_no_u64_quota(self):
        b=self.bridge();r,_,_=b.call(ceiling=(1<<128)-1,deadline=(1<<128)-1)
        self.assertEqual(r.status,0)
    def test_deadline_during_span_preserves_every_completed_prefix_store(self):
        b=self.bridge();b.f.advance_at=4;b.f.advance_ns=2
        r,after,_=b.call(data=b'x'*8192)
        self.assertEqual((r.status,r.constructed,r.construction_started,r.stores_completed),(2,0,1,4096))
        self.assertEqual(after,b'x'*4096+b'\xa5'*4096)
        self.assertEqual((r.checked_ns.integer(),b.f.releases),(102,1))
    def test_validation_clock_safepoint_is_not_a_span_quota(self):
        b=self.bridge();b.f.now=101
        r,_,owner=b.call(new=True,data=bytes(1025),count=1025)
        self.assertEqual((r.status,b.f.holds,b.f.maps,r.constructed),(2,0,0,0))
        self.assertFalse(owner.address)
        b=self.bridge();r,after,owner=b.call(new=True,data=bytes(1025),count=1025)
        self.release(owner)
        self.assertEqual((r.status,r.stores_completed,len(after)),(0,1025,1025))
    def test_partial_backing_acquisition_is_retained_and_not_relabelled(self):
        b=self.bridge();b.f.map_error=errno.ENOMEM;b.f.fail_map_index=2
        wire=C.create_string_buffer(var(4,0));src=C.create_string_buffer(b'xy')
        owners=(Owner*2)(Owner(),Owner())
        spans=(Span*2)(Span(0,0,C.addressof(src),1),Span(1,0,C.addressof(src)+1,1))
        q=Request(2,1,1,Wire(C.addressof(wire),9,9,0,0,U128()),U128.natural(7),
            U128.natural(0),U128.natural(101),owners,2,spans,2)
        r=Result();status=b.lib.jaydb_field_construct_v2(C.byref(q),C.addressof(b.view),b.size,C.byref(r))
        self.release(owners[0])
        self.assertFalse(owners[1].address)
        self.assertEqual((status,r.backing_error,r.acquired_bytes,r.construction_started,b.f.releases),
                         (6,errno.ENOMEM,4096,0,1))
        self.assertEqual(C.string_at(owners[0].address,1),b'\0')
    def test_nonzero_wire_position_and_original_zero_counts_are_preserved(self):
        b=self.bridge()
        for tag in [4,5,6]:
            r,_,_=b.call(wire=b'prefix'+var(tag,0),position=6)
            self.assertEqual((r.status,r.position,r.quantity),(0,6,0))
    def test_destination_source_alias_refused_before_hold(self):
        b=self.bridge();wire=C.create_string_buffer(b'\0');dest=C.create_string_buffer(32)
        owner=(Owner*1)(Owner(C.addressof(dest),32))
        spans=(Span*1)(Span(0,0,C.addressof(dest),8))
        q=Request(2,1,1,Wire(C.addressof(wire),1,1,0,0,U128()),U128.natural(7),
            U128.natural(100),U128.natural(101),owner,1,spans,1)
        r=Result();status=b.lib.jaydb_field_construct_v2(C.byref(q),C.addressof(b.view),b.size,C.byref(r))
        self.assertEqual((status,b.f.holds,r.constructed),(5,0,0))
    def test_span_destinations_may_be_independent_real_arena_leaves(self):
        b=self.bridge();wire=C.create_string_buffer(var(4,0));src=C.create_string_buffer(b'xy')
        owners=(Owner*2)(Owner(),Owner())
        spans=(Span*2)(Span(0,0,C.addressof(src),1),Span(1,0,C.addressof(src)+1,1))
        q=Request(2,1,1,Wire(C.addressof(wire),9,9,0,0,U128()),U128.natural(7),
            U128.natural(100),U128.natural(101),owners,2,spans,2)
        r=Result();status=b.lib.jaydb_field_construct_v2(C.byref(q),C.addressof(b.view),b.size,C.byref(r))
        for o in owners:self.release(o)
        self.assertEqual((status,b.f.maps_at_final,r.acquired_bytes),(0,2,8192))
        self.assertEqual(C.string_at(owners[0].address,1)+C.string_at(owners[1].address,1),b'xy')
    def test_real_untraced_environment_refuses_and_cleans_hold_path(self):
        r,data,_=self.bridge(True).call(ceiling=(1<<128)-1,deadline=time.monotonic_ns()+10**9)
        self.assertEqual((r.status,r.instrument_error,r.constructed),(4,errno.ENOTSUP,0))
        self.assertEqual(data,b'\xa5'*len(data))
    def test_real_ptrace_incomplete_refuses_after_actual_acquisition_preserving_active_window(self):
        sys.path.insert(0,str(ROOT))
        from tools.accounting.build import build
        library,tracer=build(self.directory/'accounting')
        probe=self.directory/'probe.py'
        probe.write_text('''import sys,time,json,ctypes as C,os
sys.path.insert(0,sys.argv[1]);sys.path.insert(0,sys.argv[1]+"/tests/native")
from test_field import Bridge
from tools.accounting.client import Library
acct=Library(sys.argv[2]);b=Bridge(sys.argv[3]);start=acct.window_begin()
r,data,owner=b.call(new=True,ceiling=0,deadline=time.monotonic_ns()+10**10,scope=start.scope_id)
assert (r.status,r.constructed,r.construction_started)==(3,0,0),(r.status,r.instrument_error)
assert r.acquired_bytes==4096 and owner.address and data==bytes(len(data))
assert r.window.snapshot.flags&2 and r.window.state==1
assert r.window.scope_id.integer()==start.scope_id
child=os.fork()
if child==0:os._exit(0)
assert os.waitpid(child,0)[1]==0 # a leaked hold would keep this peer stopped
active=acct.window_barrier();assert active.state==1
closed=acct.window_end();assert closed.state==2
next_scope=acct.window_begin();assert next_scope.scope_id!=start.scope_id
acct.window_end()
time_scope=acct.window_begin()
expired=time.monotonic_ns()-1
late,unchanged,no_owner=b.call(new=True,ceiling=0,deadline=expired,scope=time_scope.scope_id)
assert late.status==2 and late.checked_ns.integer()>=expired and not late.constructed
assert not no_owner.address and late.acquired_bytes==0
assert acct.window_barrier().state==1
acct.window_end()
libc=C.CDLL(None);libc.munmap.argtypes=[C.c_void_p,C.c_size_t];assert libc.munmap(owner.address,owner.capacity)==0
b.close()
print(json.dumps({"incompleteRefused":True,"actualBackingAcquired":True,"noFieldStores":True,"windowRemainedActive":True,"holdReleased":True}))
''')
        run=subprocess.run([str(tracer),'--report',str(self.directory/'real.jsonl'),'--',
            sys.executable,'-B',str(probe),str(ROOT),str(library),str(self.production)],text=True,capture_output=True,timeout=40)
        self.assertEqual(run.returncode,0,run.stderr+run.stdout)
        evidence=json.loads(run.stdout);self.assertTrue(all(evidence.values()))
        (ROOT/'tests/native/evidence/field-production-audit.json').write_text(json.dumps(self.report,indent=2)+'\n')
        (ROOT/'tests/native/evidence/field-real-negative.json').write_text(json.dumps(evidence,indent=2)+'\n')

if __name__=='__main__':unittest.main(verbosity=2)
