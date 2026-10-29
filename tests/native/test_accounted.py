"""Same-Book native lowering. Positive snapshots are FIXTURES only.

Production ptrace must refuse INCOMPLETE before any decoded-field store.
Run accounted_gate.mjs and build_accounted_evidence.py before this suite.
"""
import ctypes as C
import errno
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import time
import unittest

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT));sys.path.insert(0,str(Path(__file__).parent))
from tools.native.accounted import Host,Result,Descriptor,Ns128,Receipt,Progress,read_progress,install_accounted,IncompleteIntegration
from tools.service.abi import Module,RequestV3,NativeFailure
from test_native import unlimited_main_stack
from test_field import Fixture,var
from tools.service.loading import Runtime as LoadingRuntime
from tools.service.lifecycle import LifecycleRuntime
install_accounted(Module)
E=ROOT/'tests/native/evidence'
# Explicit test installation from the offline evidence builder. Importing the
# test never compiles a loader, and every subprocess probe uses the same pin.
LifecycleRuntime.load(E/'accounted-lifecycle.so',
    loading_runtime=LoadingRuntime.load(E/'accounted-loading.so'))
spec=importlib.util.spec_from_file_location('accounted_build',ROOT/'tools/native/build.py')
BUILD=importlib.util.module_from_spec(spec);spec.loader.exec_module(BUILD)

def word(n):return Ns128(n&((1<<64)-1),n>>64)

class LowModule(Module):
    def __init__(self,path,*,fixture=False):
        super().__init__(path)
        lib=self.library
        lib.jaydb_native_run_accounted_v3.argtypes=[C.POINTER(RequestV3),C.POINTER(Host),C.POINTER(Result)]
        lib.jaydb_native_run_accounted_v3.restype=C.c_uint32
        lib.jaydb_native_describe_accounted_v3.restype=C.POINTER(Descriptor)
        if fixture:
            lib.jaydb_recipe_fixture.restype=C.POINTER(Fixture)
            self.f=lib.jaydb_recipe_fixture().contents
    def accounted(self,data,*,scope=7,ceiling=100,deadline=None,execution_deadline=0,preparation_deadline=0,
                  execution_budget=10**10):
        if deadline is None:deadline=time.monotonic_ns()+10**10
        inp=(C.c_uint8*max(1,len(data))).from_buffer_copy(data or b'\0')
        req=RequestV3(3,1,inp,len(data),2**64-1,0,0,0,word(10**10),word(execution_budget),word(10**10))
        host=Host(1,word(scope),word(ceiling),(Ns128*3)(word(deadline),word(execution_deadline),word(preparation_deadline)))
        out=Result()
        try:
            with unlimited_main_stack():
                status=self.library.jaydb_native_run_accounted_v3(C.byref(req),C.byref(host),C.byref(out))
            assert status==out.native.status
            data=C.string_at(out.native.output,out.native.output_len) if out.native.output_len else b''
        finally:
            if out.native.lease:assert self.library.jaydb_native_release_v3(out.native.lease)==0
        return out,data

class AccountedTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        checked=json.loads((E/'accounted-codec.c.checked.json').read_text())
        assert checked['primary'] and checked['bendtt'] and checked['sameCheckedBook']
        assert hashlib.sha256((E/'accounted-codec.c').read_bytes()).hexdigest()==checked['cSha256']
        for name in ['production','fixture']:
            report=json.loads((E/f'accounted-{name}.so.json').read_text())
            assert report['sourceSha256']==checked['cSha256'], 'Rebuild the module for this exact same-Book C'
        cls.m=LowModule(E/'accounted-fixture.so',fixture=True)
        cls.old=Module(E/'accounted-legacy.so')
    @classmethod
    def tearDownClass(cls):cls.m.close();cls.old.close()
    def setUp(self):
        self.m.f=self.m.library.jaydb_recipe_fixture().contents
    def legacy(self,data):
        with unlimited_main_stack():
            return self.__class__.old.run(data,capacity=2**64-1,memory=100<<20,timeout_ns=10**10)
    def compare(self,data):
        r,value=self.m.accounted(data)
        self.assertEqual(r.native.status,0,(data,r.native.status,r.native.runtime_code,r.field.status,r.field.instrument_error))
        self.assertEqual(value,self.legacy(data),data)
        return r,value
    def test_layout_and_actual_guarded_c_from_same_checked_book(self):
        d=self.m.library.jaydb_native_describe_accounted_v3().contents
        self.assertEqual((C.sizeof(Host),C.sizeof(Result),d.host_bytes,d.result_bytes),(88,656,88,656))
        text=(E/'accounted-codec.c').read_text();audit=BUILD.verify_accounted_lowering(text)
        self.assertEqual(len(audit['entries']),1)
        self.assertTrue(audit['dominatingPrivateReturn'])
        snap=self.m.accounted(b'\0')[0].field.window.snapshot
        self.assertEqual((snap.abi,snap.sequence.natural(),snap.current.natural(),snap.flags),(1,12,100,9))
        self.assertEqual((snap.peak_flags,type(snap).flags.offset),(0,112))
        for bad in [text.replace('if (jaydb_accounted_enabled()) {','if (false) {'),
                    text.replace('#define WL_RETN(N)  { rn = (N); sp -= LANE_STEP; WL_DYN((u32)STK(0)); }',
                        '#define WL_RETN(N) {}'),
                    text.replace('WL_RETN(2);\n    } else {',';\n    } else {'),
                    text.replace('// JAYDB_NATIVE_ACCOUNTED_ENTRY_V1 ','// REMOVED '),
                    text.replace('CID_Dados_Campo};','CID_Dados_VInt};')]:
            with self.assertRaises(BUILD.BuildError):BUILD.verify_accounted_lowering(bad)
    def test_fixture_primitives_immediates_empty_variable_guards(self):
        for data in [b'\0',b'\1',b'\2',b'\3'+bytes(8),b'\3'+b'\xff'*8,
                     var(4,0),var(5,0),var(6,0)]:
            with self.subTest(data=data):
                r,value=self.compare(data)
                self.assertEqual(value,data)
                self.assertGreater(r.field_calls,0)
                self.assertEqual(r.field_calls,r.field_completed)
                self.assertEqual(r.field.quantity,8 if data[0]==3 else 0)
                self.assertEqual((r.field.position,r.field.tag,r.field.length_checked),(0,data[0],1))
    def test_fixture_text_unicode_reverse_list_record_nested_and_partial(self):
        texts=[b'',b'a',b'hello','á𝄞\0'.encode(),b'\xc0\x80',b'\xed\xa0\x80',b'\xf4\x90\x80\x80',b'a\xf0\x90']
        texts.extend(bytes.fromhex(s) for s in ['c280','dfbf','e0a080','efbfbf',
            'f0908080','f48fbfbf','80','e08080','f5808080','c261'])
        values=[var(4,len(s),s) for s in texts]
        values += [var(5,2,b'\0\2'),var(6,2,var(4,1,b'a')+b'\0'+var(4,1,b'b')+b'\2'),
            var(6,1,var(4,2,b'_0')+var(5,1,var(4,3,b'abc'))),
            var(6,1,var(4,1,b'0')+b'\0'),var(6,2,var(4,1,b'b')+b'\0'+var(4,1,b'a')+b'\0')]
        values += [var(6,1,var(4,len(name),name)+b'\0') for name in
            [b'_',b'a0',b'a'*64,b'a'*65,b'',b'bad-name','á'.encode()]]
        values += [var(6,2,var(4,1,b'a')+b'\0'+var(4,1,b'a')+b'\0')]
        for data in values:
            with self.subTest(data=data):
                r,value=self.compare(data)
                if data[0] in (5,6) and value[0] not in (253,254):
                    self.assertEqual((r.field.position,r.field.quantity),(0,int.from_bytes(data[1:9],'big')))
        r,value=self.compare(var(4,2,b'a\xff'))
        self.assertEqual(value,b'\xfe');self.assertGreater(r.field_completed,0)
        self.assertEqual((r.field.position,r.field.quantity),(0,2))
    def test_fixture_context_uses_actual_bs_and_multiple_decodes(self):
        r,value=self.compare(b'\xfa'+var(4,1,b'a'))
        self.assertEqual((r.decoder_calls,r.decoder_completed,r.field.position,r.field.quantity),(1,1,0,1))
        r,value=self.compare(b'\xf9'+var(5,1,b'\0'))
        self.assertEqual((r.decoder_calls,r.decoder_completed,r.decode_id),(2,2,2))
        self.assertEqual(value,var(5,1,b'\0')*2)
        r,value=self.compare(b'\xf3ignored private input')
        self.assertEqual((value,r.decoder_calls,r.field.quantity,r.field.position),(b'\0',1,0,0))
        p=read_progress(self.m)
        self.assertEqual((p.wire_size,p.wire_copied,p.cursor),(1,1,1))
    def test_fixture_actual_body_limit_minimum_and_original_ancestor_counts(self):
        for data,expected in [(var(4,23,b'x'*23),None),(var(4,24,b'x'*24),b'\xfd'),
                (var(4,24,b'x'),b'\xfd'),(var(4,22,b'x'),b'\xfe'),
                (var(5,2,var(4,15,b'abcd')+b'\0'),b'\xfd'),
                (var(5,2,var(4,9,b'abcd')+b'\0'),b'\xfe')]:
            r,value=self.compare(b'\xf5'+data)
            self.assertEqual(value,data if expected is None else expected)
    def test_primitive_pending_error_priority_matches_original_codec(self):
        cases=[(b'\xf5'+var(5,3,var(4,5,b'abcde')+b'\3'+bytes(8)),b'\xfe'),
               (var(5,12,b'\3'+bytes(8)+var(4,2**64-1)),b'\xfd'),
               (b'\xf5'+var(6,2,var(4,1,b'a')+b'\3'+bytes(8)+b'\4\0\0'),b'\xfe')]
        for body,expected in cases:
            with self.subTest(body=body.hex()):
                r,value=self.compare(body)
                self.assertEqual(value,expected)
                self.assertGreater(r.logical_claims,0)
                self.assertEqual(r.field_completed,r.field_calls)
                # The original integer is constructed, followed by its
                # parent's accumulator. The later malformed header may fail
                # before another recipe; the last origin can be that parent.
                self.assertGreaterEqual(r.field_calls,5)
    def test_progress_records_raw_copy_utf8_prefix_and_real_runtime_clock(self):
        r,value=self.compare(var(4,3,b'a\xf0\x90'))
        p=read_progress(self.m)
        self.assertEqual(C.sizeof(Progress),104)
        self.assertEqual((p.phase,p.wire_size,p.wire_copied,p.cursor),(7,12,12,12))
        self.assertEqual((p.scalar_start,p.utf8_consumed,p.utf8_needed),(10,2,2))
        self.assertEqual(p.decode_id,r.decode_id)
        self.assertGreaterEqual(p.sampled_ns,r.stage_started_ns.natural())
        self.assertLessEqual(p.sampled_ns,r.returned_ns.natural())
    def test_runtime_time_preserves_decoder_metadata_prefix_and_original_epoch(self):
        # Synthetic memory observations only; the deadline and poll clock here
        # are real CLOCK_MONOTONIC. No artificial epoch renewal or sleep hook.
        r,_=self.m.accounted(b'\xf7'+var(4,65536,b'x'*65536),execution_budget=10**6)
        p=read_progress(self.m)
        self.assertEqual((r.native.status,r.native.stage),(3,1))
        self.assertEqual(r.decision_deadline_ns.natural()-r.stage_started_ns.natural(),10**6)
        if not p.decode_id:self.skipTest('Original deadline expired before decoder entry; no prefix invented')
        self.assertEqual(p.decode_id,1)
        self.assertIn(p.phase,(1,2,3,4,5,6))
        self.assertGreater(p.wire_size,0)
        self.assertLessEqual(p.wire_copied,p.wire_size)
        self.assertLessEqual(p.cursor,p.wire_size)
        self.assertGreaterEqual(p.sampled_ns,r.decision_deadline_ns.natural())
        (E/'accounted-metadata-time.json').write_text(json.dumps({
            **p.__dict__,'deadline_ns':r.decision_deadline_ns.natural(),
            'native_status':r.native.status,'syntheticMemoryObservation':True},indent=2)+'\n')
    def test_fixture_client_invalid_intermediate_value_is_not_wire_field(self):
        r,value=self.compare(b'\xf8')
        self.assertEqual((value,r.decoder_calls,r.field_calls),(b'X',0,0))
    def test_fixture_no_depth_arity_or_length_quota(self):
        for data in [var(5,513,bytes(513)),var(4,4097,b'x'*4097),var(5,1)*513+b'\0']:
            with self.subTest(size=len(data)):self.compare(data)
    def test_fixture_equality_strict_excess_and_incomplete_no_claim_or_store(self):
        r,value=self.compare(b'\3'+bytes(8))
        self.assertGreater(r.logical_claims,0);self.assertEqual(r.field.window.peak.natural(),100)
        for flags,ceiling,expected in [(9,99,1),(11,0,3)]:
            self.m.f.flags=flags
            r,value=self.m.accounted(b'\3'+bytes(8),ceiling=ceiling)
            self.assertEqual((r.native.status,r.native.runtime_code,r.field.status),(11,0x4649454c,expected))
            self.assertEqual((r.field_calls,r.field_completed,r.logical_claims,r.field.stores_completed),(1,0,0,0))
            self.assertEqual((r.field.construction_started,r.field.constructed,len(value)),(0,0,0))
            self.assertEqual(self.m.f.holds,self.m.f.releases)
    def test_deadline_receipt_preserves_past_epoch_even_on_native_failure(self):
        deadline=time.monotonic_ns()-1
        r,value=self.m.accounted(b'\0',deadline=deadline)
        self.assertEqual((r.native.status,r.native.stage,r.timing_flags,r.decoder_calls),(3,0,3,0))
        self.assertEqual(r.decision_deadline_ns.natural(),deadline)
        self.assertGreaterEqual(r.stage_started_ns.natural(),deadline)
        self.assertGreaterEqual(r.returned_ns.natural(),r.stage_started_ns.natural())
    def test_real_original_execution_and_preparation_deadlines_survive_failure(self):
        for stage,prefix in [(1,247),(2,246)]:
            original=time.monotonic_ns()-123
            options={'execution_deadline':original} if stage==1 else {'preparation_deadline':original}
            r,value=self.m.accounted(bytes([prefix,0]),**options)
            self.assertEqual((r.native.status,r.native.stage,r.timing_flags,r.decoder_calls),(3,stage,3,0))
            self.assertEqual(r.decision_deadline_ns.natural(),original)
            self.assertGreaterEqual(r.stage_started_ns.natural(),original)
            self.assertGreaterEqual(r.returned_ns.natural(),r.stage_started_ns.natural())
        original=time.monotonic_ns()+10**10
        r,value=self.m.accounted(b'\xf7\0',execution_deadline=original)
        self.assertEqual((r.native.status,r.native.stage,r.decision_deadline_ns.natural()),(0,1,original))
        self.assertEqual(self.m.f.deadlines[1],original)
        r,value=self.m.accounted(b'\xf6\0')
        self.assertEqual((r.native.status,r.native.stage),(0,2))
        self.assertEqual(r.decision_deadline_ns.natural()-r.stage_started_ns.natural(),10**10)
    def test_adapter_native_failure_carries_exact_interrupted_stage_receipt(self):
        class Monitor:
            # SYNTHETIC preflight only. The real native CLOCK_MONOTONIC, not
            # this poll, justifies TIME before entering any field boundary.
            scope=7;ceiling=2**300
            def poll(self):pass
        m=Module(E/'accounted-production.so');self.addCleanup(m.close)
        for stage,prefix in [(0,0),(1,247),(2,246)]:
            original=time.monotonic_ns()-100
            opts={'setup_deadline_ns':original if stage==0 else time.monotonic_ns()+10**10}
            if stage==1:opts['execution_deadline_ns']=original
            if stage==2:opts['preparation_deadline_ns']=original
            with self.assertRaises(NativeFailure) as caught:
                with unlimited_main_stack():
                    m.run_accounted(bytes([prefix,0]),accounting=Monitor(),capacity=100,memory=1,
                        timeout_ns=10**10,**opts)
            receipt=caught.exception.accounted_receipt
            self.assertEqual((caught.exception.status,receipt.stage,receipt.decision_deadline_ns),(3,stage,original))
            self.assertEqual(m.last_accounted_receipt,receipt)
            self.assertEqual(caught.exception.decision_deadline_ns,original)
            self.assertEqual(receipt.decoder_calls,0)
    def test_fixture_random_malformed_prefixes_match_original_codec(self):
        rng=random.Random(4921)
        for i in range(150):
            tag=rng.randrange(7);n=rng.choice([0,1,2,3,64,2**64-1])
            data=(var(tag,n) if tag>=4 else bytes([tag]))+rng.randbytes(rng.randrange(16))
            self.compare(data)
    def test_adapter_cannot_enable_legacy_or_fixture_via_editable_report(self):
        class Monitor:
            scope=7;ceiling=2**300
            def poll(self):raise AssertionError('must fail before monitor or decoder')
        for module in [self.m,self.__class__.old]:
            with self.assertRaises(IncompleteIntegration):
                module.run_accounted(b'\0',accounting=Monitor(),capacity=100,memory=100,
                    timeout_ns=10**9,setup_deadline_ns=time.monotonic_ns()+10**9)
        old=self.__class__.old
        lib=old.library;lib.jaydb_native_run_accounted_v3.argtypes=[C.POINTER(RequestV3),C.POINTER(Host),C.POINTER(Result)]
        out=Result();host=Host(1,word(7),word(100),(Ns128*3)(word(2**100),word(0),word(0)))
        # Even a raw FFI invocation cannot select legacy decoded-field stores.
        self.assertEqual(lib.jaydb_native_run_accounted_v3(None,C.byref(host),C.byref(out)),1)
        self.assertEqual((out.decoder_calls,out.field_calls),(0,0))
        valid=LowModule(E/'accounted-legacy.so');self.addCleanup(valid.close)
        r,_=valid.accounted(b'\0')
        self.assertEqual((r.native.status,r.decoder_calls,r.field_calls),(1,0,0))
    def test_trusted_no_decoder_book_enables_private_context_without_wire_fields(self):
        path=E/'accounted-no-codec.so'
        report=json.loads(path.with_suffix('.so.json').read_text())
        checked=json.loads((E/'accounted-no-codec.c.checked.json').read_text())
        self.assertEqual(report['sourceSha256'],checked['cSha256'])
        self.assertTrue(checked['primary'] and checked['bendtt'] and checked['sameCheckedBook'])
        text=(E/'accounted-no-codec.c').read_text()
        cut=BUILD.verify_accounted_lowering(text)
        self.assertTrue(cut['decoderFree'] and cut['completeEntryCut'])
        self.assertEqual(cut['entries'],[])
        with self.assertRaises(BUILD.BuildError):
            BUILD.verify_accounted_lowering(text.replace('// JAYDB_NATIVE_ACCOUNTED_EMPTY_V1\n',''))
        contradicted=text+'// JAYDB_NATIVE_ACCOUNTED_UNCOVERED_V1 Unknown:decodificar\n'
        with self.assertRaises(BUILD.BuildError):BUILD.verify_accounted_lowering(contradicted)
        prepared,_=BUILD.prepare_source(text,None,'CID_Native_write')
        self.assertIn('#define JAYDB_ACCOUNTED_CODEC 0\n',prepared)
        self.assertIn('#define JAYDB_ACCOUNTED_NO_CODEC 1\n',prepared)
        self.assertIn('#define JAYDB_ACCOUNTED_ENTRY_COVERAGE 1\n',prepared)
        m=LowModule(path);self.addCleanup(m.close)
        self.assertEqual(m.library.jaydb_native_describe_accounted_v3().contents.lowering_version,1)
        # C context/encoder experiment only. No observation or publication is
        # claimed by native OK; complete monitoring/completion remain required.
        r,value=m.accounted(b'',ceiling=0)
        self.assertEqual((r.native.status,r.decoder_calls,r.field_calls),(0,0,0))
        self.assertGreater(r.native.charged_bytes,0)
        self.assertEqual(value,var(5,1,b'\3'+(1).to_bytes(8,'big')))
        self.assertIsNone(report['accountedRecipeAudit'])
        class PreflightFixture:
            scope=7;ceiling=2**300
            def poll(self):pass
        with unlimited_main_stack():
            actual=m.run_accounted(b'',accounting=PreflightFixture(),capacity=100,memory=0,
                timeout_ns=10**10,setup_deadline_ns=time.monotonic_ns()+10**10)
        self.assertEqual(actual,value)
        self.assertEqual(m.last_accounted_receipt.field_calls,0)
        class IncompleteMonitor:
            scope=7;ceiling=2**300
            def poll(self):raise ValueError('INCOMPLETE')
        with self.assertRaises(IncompleteIntegration):
            m.run_accounted(b'',accounting=IncompleteMonitor(),capacity=100,memory=0,
                timeout_ns=10**10,setup_deadline_ns=time.monotonic_ns()+10**10)
    def test_real_external_helper_has_no_wire_context_and_cannot_select_legacy_in_accounted(self):
        m=LowModule(E/'accounted-helper.so');self.addCleanup(m.close)
        self.assertEqual(m.library.jaydb_native_describe_accounted_v3().contents.lowering_version,0)
        r,value=m.accounted(b'\xf8')
        self.assertEqual((r.native.status,r.decoder_calls,r.field_calls),(1,0,0))
        # The source language remains general. Its ordinary pure helper call
        # and invalid intermediate client value still run through legacy V3.
        with unlimited_main_stack():
            value=m.run(b'\xf8',capacity=100,memory=100<<20,timeout_ns=10**10)
        self.assertEqual(value,b'X')
    def test_real_untraced_production_refuses_first_field(self):
        m=LowModule(E/'accounted-production.so');self.addCleanup(m.close)
        r,value=m.accounted(b'\xfa\0',ceiling=2**128-1)
        self.assertEqual((r.native.status,r.field.status,r.field.instrument_error),(11,4,errno.ENOTSUP))
        self.assertEqual((r.decoder_calls,r.field_calls,r.field_completed,r.field.stores_completed),(1,1,0,0))
        self.assertEqual((r.field.position,r.field.quantity,r.field.tag),(0,0,0))
    def test_real_ptrace_incomplete_refuses_before_first_store_and_releases(self):
        from tools.accounting.build import build
        with tempfile.TemporaryDirectory(prefix='jaydb-accounted-ptrace-') as tmp:
            directory=Path(tmp);library,tracer=build(directory/'accounting')
            probe=directory/'probe.py'
            probe.write_text('''import sys,time,os,json
sys.path.insert(0,sys.argv[1]);sys.path.insert(0,sys.argv[1]+"/tests/native")
from test_accounted import LowModule,E,Module,IncompleteIntegration,unlimited_main_stack
from tools.accounting.client import Library
from tools.service.memory import MemoryWindow
acct=Library(sys.argv[2]);m=LowModule(E/'accounted-production.so')
start=acct.window_begin()
r,value=m.accounted(b'\\xfa\\0',scope=start.scope_id,ceiling=0,deadline=time.monotonic_ns()+30*10**9)
assert (r.native.status,r.native.runtime_code,r.field.status)==(11,0x4649454c,3),(r.native.status,r.field.status,r.field.instrument_error)
assert (r.decoder_calls,r.field_calls,r.field_completed,r.logical_claims,r.field.stores_completed)==(1,1,0,0,0)
assert (r.field.position,r.field.quantity,r.field.tag)==(0,0,0)
assert r.field.window.state==1 and (r.field.window.snapshot.flags|r.field.window.peak_flags)&2,(r.field.window.state,r.field.window.snapshot.flags,r.field.window.peak_flags,r.field.instrument_error)
assert r.timing_flags==3 and r.decision_deadline_ns.natural()>r.stage_started_ns.natural()
child=os.fork()
if child==0:os._exit(0)
assert os.waitpid(child,0)[1]==0
active=acct.window_barrier();assert active.state==1
closed=acct.window_end();assert closed.state==2
again=acct.window_begin()
r2,value=m.accounted(bytes([4])+bytes(7)+bytes([2])+b'a\\xff',scope=again.scope_id,ceiling=2**128-1,deadline=time.monotonic_ns()+30*10**9)
assert (r2.field.status,r2.field.position,r2.field.quantity,r2.field.tag,r2.field_completed)==(3,0,2,4,0)
empty=Module(E/'accounted-no-codec.so')
try:
    with unlimited_main_stack():
        empty.run_accounted(b'',accounting=MemoryWindow(acct,again.scope_id,2**300),
            capacity=100,memory=0,timeout_ns=30*10**9,setup_deadline_ns=time.monotonic_ns()+30*10**9)
    raise AssertionError('NoCodec cannot use INCOMPLETE to authorize service execution')
except IncompleteIntegration:
    assert empty.last_accounted_receipt is None
empty.close()
acct.window_end();m.close()
print(json.dumps({'incomplete':True,'firstFieldStores':r.field.stores_completed,'activeAfterReturn':active.state==1,'releasedPeer':True,'partialTextOriginalN':r2.field.quantity,'noCodecIncompleteRefused':True}))
''')
            completed=subprocess.run([str(tracer),'--',sys.executable,str(probe),str(ROOT),str(library)],
                capture_output=True,text=True,timeout=90)
            self.assertEqual(completed.returncode,0,completed.stderr[-3000:]+completed.stdout[-3000:])
            report=json.loads(completed.stdout.strip().splitlines()[-1])
            self.assertTrue(report['incomplete']);self.assertEqual(report['firstFieldStores'],0)
            (E/'accounted-real-ptrace.json').write_text(json.dumps(report,indent=2)+'\n')

if __name__=='__main__':unittest.main(verbosity=2)
