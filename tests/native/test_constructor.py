"""Experimental trusted-store boundary. Synthetic snapshots are not MedicaoReal.

The real ptrace observer is tested only for INCOMPLETE refusal, not acceptance.
This is not yet instrumentation of the real Codec emitted constructors.
"""
import ctypes as C
import errno
import importlib.util
import json
import mmap
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest

ROOT=Path(__file__).resolve().parents[2]
SPEC=importlib.util.spec_from_file_location('constructor_build',ROOT/'tools/native/build_constructor.py')
BUILD=importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BUILD)
U64=C.c_uint64


class U128(C.Structure):
    _fields_=[('lo',U64),('hi',U64)]
    @classmethod
    def natural(cls,n):return cls(n&((1<<64)-1),n>>64)
    def integer(self):return self.lo|(self.hi<<64)


class Snapshot(C.Structure):
    _fields_=[('abi',U64),('sequence',U128),('current',U128),('peak',U128),
        ('monotonic_ns',U128),('peak_monotonic_ns',U128),('peak_sequence',U128),
        ('peak_flags',U64),('flags',U64)]


class Length(C.Structure):
    _fields_=[('abi',U64),('checked',U64),('position',U64),('quantity',U64)]


class Span(C.Structure):
    _fields_=[('destination',C.c_void_p),('source',C.c_void_p),('bytes',U64)]


class Result(C.Structure):
    _fields_=[('status',U64),('constructed',U64),('instrument_error',U64),
        ('release_error',U64),('clock_error',U64),('constructor_id',U64),
        ('site_id',U64),('position',U64),('quantity',U64),('memory',Snapshot),('checked_ns',U128)]


class Bridge:
    def __init__(self,path,*,fixture=False):
        self.lib=C.CDLL(str(path))
        self.lib.jaydb_constructor_stack_bytes.restype=U64
        self.size=self.lib.jaydb_constructor_stack_bytes()
        self.stack=mmap.mmap(-1,self.size)
        self.stack[:]=bytes(self.size)
        self.stack_view=C.c_char.from_buffer(self.stack)
        self.lib.jaydb_constructor_transfer.argtypes=[U64,U64,C.POINTER(Length),C.POINTER(Span),
            U64,U128,U128,C.c_void_p,U64,C.POINTER(Result)]
        self.lib.jaydb_constructor_transfer.restype=U64
        if fixture:
            self.lib.jaydb_constructor_fixture.argtypes=[U64]*5
            self.lib.jaydb_constructor_watch.argtypes=[C.c_void_p,U64]
            self.lib.jaydb_constructor_fixture_count.argtypes=[C.c_uint]
            self.lib.jaydb_constructor_fixture_count.restype=U64
    def configure(self,*,flags=9,current=100,now=100,op=(1<<64)-1,error=0):
        self.lib.jaydb_constructor_fixture(flags,current,now,op,error)
    def transfer(self,data=b'real destination bytes',*,ceiling=100,deadline=101,checked=1):
        source=C.create_string_buffer(data)
        destination=(C.c_ubyte*len(data))(*([0xa5]*len(data)))
        spans=(Span*1)(Span(C.addressof(destination),C.addressof(source),len(data)))
        if hasattr(self.lib,'jaydb_constructor_watch'):
            self.lib.jaydb_constructor_watch(destination,len(data))
        result=Result();length=Length(1,checked,17,len(data))
        status=self.lib.jaydb_constructor_transfer(65537,9,C.byref(length),spans,1,
            U128.natural(ceiling),U128.natural(deadline),C.addressof(self.stack_view),self.size,C.byref(result))
        assert status==result.status
        return result,bytes(destination)
    def close(self):
        del self.stack_view
        self.stack.close()


class ConstructorTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp=tempfile.TemporaryDirectory(prefix='jaydb-constructor-tests-')
        cls.directory=Path(cls.temp.name)
        cls.production=cls.directory/'production.so';cls.fixture=cls.directory/'fixture.so'
        cls.report=BUILD.build(cls.production)
        BUILD.build(cls.fixture,test_fixture=ROOT/'tests/native/constructor_fixture.c')
    @classmethod
    def tearDownClass(cls):cls.temp.cleanup()
    def bridge(self,*,production=False):
        b=Bridge(self.production if production else self.fixture,fixture=not production)
        self.addCleanup(b.close)
        return b

    def test_production_is_audited_leaf_without_callbacks_or_library_dependencies(self):
        self.assertTrue(self.report['criticalIsLeaf'])
        self.assertFalse(self.report['testFixture'])
        self.assertGreater(self.report['criticalFrameBytes'],0)
        self.assertGreaterEqual(self.report['stackBytes'],self.report['criticalFrameBytes']+8)
        self.assertEqual(C.sizeof(Snapshot),120)
        symbols=subprocess.check_output(['nm','-D',str(self.production)],text=True)
        self.assertNotIn(' U ',symbols)
        self.assertNotIn('test_marker',symbols)

    def test_synthetic_equality_constructs_only_after_both_barriers(self):
        bridge=self.bridge();bridge.configure()
        result,data=bridge.transfer()
        self.assertEqual((result.status,result.constructed,data),(0,1,b'real destination bytes'))
        self.assertEqual(result.memory.current.integer(),100)
        self.assertEqual((result.constructor_id,result.site_id,result.position,result.quantity),(65537,9,17,len(data)))
        self.assertEqual(bridge.lib.jaydb_constructor_fixture_count(0),1)
        self.assertEqual(bridge.lib.jaydb_constructor_fixture_count(1),0)

    def test_synthetic_actual_excess_before_construction_keeps_destination_raw(self):
        bridge=self.bridge();bridge.configure(current=101)
        result,data=bridge.transfer()
        self.assertEqual((result.status,result.constructed,result.memory.current.integer()),(1,0,101))
        self.assertEqual(data,bytes([0xa5])*len(data))
        self.assertEqual(bridge.lib.jaydb_constructor_fixture_count(0),1)

    def test_synthetic_incomplete_dead_owner_or_unheld_is_never_memory_excess(self):
        bridge=self.bridge()
        for flags in [11,13,1,8,0]:
            bridge.configure(flags=flags,current=1000)
            result,data=bridge.transfer()
            self.assertEqual((result.status,result.constructed),(3,0))
            self.assertEqual(data,bytes([0xa5])*len(data))

    def test_synthetic_deadline_equality_and_unconfirmed_marker_timeout(self):
        bridge=self.bridge();bridge.configure(now=101)
        result,data=bridge.transfer()
        self.assertEqual((result.status,result.constructed),(2,0))
        self.assertEqual(data,bytes([0xa5])*len(data))
        for now,expected in [(100,4),(101,2)]:
            bridge.configure(op=0,error=errno.ETIMEDOUT,now=now)
            result,data=bridge.transfer()
            self.assertEqual((result.status,result.constructed),(expected,0))
            self.assertEqual(data,bytes([0xa5])*len(data))
            self.assertEqual(bridge.lib.jaydb_constructor_fixture_count(0),1)

    def test_synthetic_release_failure_does_not_revoke_constructed_bytes(self):
        bridge=self.bridge();bridge.configure(op=6,error=errno.EIO)
        result,data=bridge.transfer()
        self.assertEqual((result.status,result.constructed,result.release_error,data),
                         (0,1,errno.EIO,b'real destination bytes'))

    def test_missing_prior_length_marker_refuses_without_any_construction(self):
        bridge=self.bridge();bridge.configure()
        result,data=bridge.transfer(checked=0)
        self.assertEqual((result.status,result.constructed),(5,0))
        self.assertEqual(data,bytes([0xa5])*len(data))
        self.assertEqual(bridge.lib.jaydb_constructor_fixture_count(0),0)

    def test_vector_has_no_arity_247_quota_and_preserves_each_source(self):
        bridge=self.bridge();bridge.configure()
        count=513
        source=(C.c_ubyte*count)(*(i%256 for i in range(count)))
        destination=(C.c_ubyte*count)(*([0xa5]*count))
        spans=(Span*count)(*(Span(C.addressof(destination)+i,C.addressof(source)+i,1) for i in range(count)))
        bridge.lib.jaydb_constructor_watch(destination,count)
        length=Length(1,1,0,count);result=Result()
        status=bridge.lib.jaydb_constructor_transfer(70000,12,C.byref(length),spans,count,
            U128.natural(100),U128.natural(101),C.addressof(bridge.stack_view),bridge.size,C.byref(result))
        self.assertEqual((status,result.constructed,bytes(destination)),(0,1,bytes(source)))
        self.assertEqual(bridge.lib.jaydb_constructor_fixture_count(1),0)

    def test_real_untraced_environment_cannot_authorize_construction(self):
        result,data=self.bridge(production=True).transfer(ceiling=(1<<128)-1,deadline=time.monotonic_ns()+10**9)
        self.assertEqual((result.status,result.constructed,result.instrument_error),(4,0,errno.ENOTSUP))
        self.assertEqual(data,bytes([0xa5])*len(data))

    def test_real_observer_incomplete_refuses_and_releases_hold(self):
        sys.path.insert(0,str(ROOT))
        from tools.accounting.build import build as accounting_build
        library,tracer=accounting_build(self.directory/'accounting')
        probe=self.directory/'probe.py'
        probe.write_text('''import sys,time,json
sys.path.insert(0,sys.argv[1]);sys.path.insert(0,sys.argv[1]+"/tests/native")
from test_constructor import Bridge
from tools.accounting.client import Library
accounting=Library(sys.argv[2]);bridge=Bridge(sys.argv[3])
result,data=bridge.transfer(ceiling=2**128-1,deadline=time.monotonic_ns()+10**10)
assert (result.status,result.constructed)==(3,0),(result.status,result.instrument_error)
assert data==bytes([0xa5])*len(data)
assert result.memory.flags&2
held=accounting.hold_begin();accounting.hold_release()
bridge.close()
print(json.dumps({"incompleteRefused":True,"noDestinationStores":True,"holdReleased":True}))
''')
        report=self.directory/'observer.jsonl'
        result=subprocess.run([str(tracer),'--report',str(report),'--',sys.executable,'-B',str(probe),
            str(ROOT),str(library),str(self.production)],capture_output=True,text=True,timeout=30)
        self.assertEqual(result.returncode,0,result.stderr+result.stdout)
        self.assertEqual(json.loads(result.stdout),{'incompleteRefused':True,'noDestinationStores':True,'holdReleased':True})
        (ROOT/'tests/native/evidence/constructor-production-audit.json').write_text(json.dumps(self.report,indent=2)+'\n')


if __name__=='__main__':unittest.main(verbosity=2)
