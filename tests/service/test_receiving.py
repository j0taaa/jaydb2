from __future__ import annotations
import ctypes as C
from dataclasses import replace
import errno
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
from unittest.mock import patch

from tools.accounting.client import NativeWindowSnapshot,WindowSnapshot,U128
from tools.service.build_receiving import build
from tools.service.receiving import Receiver,IncompleteReceiving,ChunkRequest,ChunkReceipt

ROOT=Path(__file__).resolve().parents[2]
END=(1<<63)*1_000_000_000

class Counter:
    def __init__(self,library):
        self.library=library
        library.jaydb_receiving_test_read.argtypes=[C.POINTER(NativeWindowSnapshot)]
    def window_read(self):
        out=NativeWindowSnapshot()
        self.library.jaydb_receiving_test_read(C.byref(out))
        return WindowSnapshot.native(out)

class ReceivingTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(prefix='jaydb-receiving-test-')
        self.path=Path(self.tmp.name)/'receiving.so'
        build(self.path,test_fixture=ROOT/'tests/service/receiving_fixture.c')
        self.lib=C.CDLL(str(self.path))
        self.counter=Counter(self.lib)
        self.receiver=Receiver(self.path,self.counter,allow_fixture=True)
        self.fds=[]
    def tearDown(self):
        self.receiver.close()
        import _ctypes
        _ctypes.dlclose(self.lib._handle)
        for fd in self.fds:
            os.close(fd)
        self.tmp.cleanup()
    def pipe(self,data,*,closed=True):
        r,w=os.pipe();self.fds.append(r)
        if data:os.write(w,data)
        if closed:os.close(w)
        else:self.fds.append(w)
        return r
    def receive(self,data,*,closed=True,duration=1_000_000_000,limit=65536,memory=100):
        return self.receiver.receive(self.pipe(data,closed=closed),duration_ns=duration,
            instrument_deadline_ns=END,message_limit=limit,memory_ceiling=memory)
    def test_eof_between_messages_opens_no_scope(self):
        self.assertIsNone(self.receive(b''))
        self.assertIsNone(self.receiver.pending)
        self.assertEqual(self.counter.window_read().state,0)
    def test_complete_zero_body_uses_one_original_epoch(self):
        before=time.monotonic_ns()
        frame=self.receive(bytes(8))
        self.assertTrue(frame.complete)
        self.assertEqual(frame.body,b'')
        self.assertEqual(frame.header,bytes(8))
        self.assertLessEqual(before,frame.start.started_ns)
        self.assertLessEqual(frame.start.started_ns,frame.start.received_ns)
        self.assertEqual(frame.start.deadline_ns,frame.start.started_ns+1_000_000_000)
        self.assertTrue(self.counter.window_read().active)

    def chunk_signal(self,nth):
        function=self.lib.jaydb_receiving_test_chunk_signal
        function.argtypes=[C.c_uint64,C.c_int]
        function(nth,signal.SIGUSR1)

    def test_signal_after_body_read_retains_exact_bytes_and_next_message(self):
        first=(3).to_bytes(8,'big')+b'abc'
        second=(3).to_bytes(8,'big')+b'DEF'
        fd=self.pipe(first+second)
        self.chunk_signal(2) # header tail, then body
        previous=signal.signal(signal.SIGUSR1,
            lambda *_:(_ for _ in ()).throw(InterruptedError('after durable body read')))
        try:
            frame=self.receiver.receive(fd,duration_ns=10**9,instrument_deadline_ns=END,
                message_limit=100,memory_ceiling=100)
        finally:signal.signal(signal.SIGUSR1,previous)
        self.assertEqual((frame.status,frame.close_channel,frame.header,frame.body),
            ('falha',False,first[:8],b'abc'))
        self.assertTrue(frame.framed)
        self.assertIsInstance(frame.error,InterruptedError)
        chunk=self.receiver.pending_chunk
        self.assertEqual((chunk.state,chunk.received,chunk.data),(2,3,b'abc'))
        self.lib.jaydb_receiving_test_close()
        following=self.receiver.receive(fd,duration_ns=10**9,instrument_deadline_ns=END,
            message_limit=100,memory_ceiling=100)
        self.assertEqual(following.body,b'DEF')
        self.assertNotEqual(frame.start.scope,following.start.scope)

    def test_signal_after_empty_body_header_keeps_framing(self):
        self.chunk_signal(1)
        previous=signal.signal(signal.SIGUSR1,
            lambda *_:(_ for _ in ()).throw(InterruptedError('after durable header read')))
        try:frame=self.receive(bytes(8))
        finally:signal.signal(signal.SIGUSR1,previous)
        self.assertEqual((frame.status,frame.close_channel,frame.header,frame.body),
            ('falha',False,bytes(8),b''))
        self.assertTrue(frame.framed)

    def test_exception_keeps_raw_chunk_before_python_prefix_copy(self):
        fd=self.pipe((3).to_bytes(8,'big')+b'abc'+b'next')
        self.chunk_signal(2)
        previous=signal.signal(signal.SIGUSR1,
            lambda *_:(_ for _ in ()).throw(RuntimeError('after durable read')))
        try:
            with self.assertRaisesRegex(RuntimeError,'after durable read'):
                self.receiver.receive(fd,duration_ns=10**9,instrument_deadline_ns=END,
                    message_limit=100,memory_ceiling=100)
        finally:signal.signal(signal.SIGUSR1,previous)
        chunk=self.receiver.pending_chunk
        self.assertEqual((chunk.state,chunk.received,chunk.data),(2,3,b'abc'))
        self.assertEqual(os.read(fd,4),b'next')
        self.assertTrue(self.counter.window_read().active)
        with self.assertRaises(IncompleteReceiving):
            self.receiver.receive(fd,duration_ns=10**9,instrument_deadline_ns=END,
                message_limit=100,memory_ceiling=100)

    def test_reapplying_returned_chunk_never_appends_twice(self):
        frame=self.receive((3).to_bytes(8,'big')+b'abc')
        owner=self.receiver._last_chunk
        self.receiver._apply_chunk(owner)
        self.receiver._apply_chunk(owner)
        self.assertEqual(bytes(self.receiver._read_prefix),b'abc')
        self.assertEqual(frame.body,b'abc')

    def test_time_after_last_byte_preserves_message_synchronization(self):
        original=self.receiver._poll
        delayed=[]
        def poll(monitor):
            result=original(monitor)
            if self.receiver._read_prefix==b'abc' and not delayed:
                delayed.append(True)
                time.sleep(.05)
            return result
        with patch.object(self.receiver,'_poll',side_effect=poll):
            frame=self.receive((3).to_bytes(8,'big')+b'abc',duration=30_000_000)
        self.assertTrue(delayed)
        self.assertGreaterEqual(time.monotonic_ns(),frame.start.deadline_ns)
        self.assertEqual((frame.status,frame.close_channel,frame.body),('limite',False,b'abc'))
        self.assertTrue(frame.framed)

    def test_native_chunk_receipt_reentry_never_reads_twice(self):
        fd=self.pipe(b'abcDEF')
        buffer=C.create_string_buffer(3)
        request=ChunkRequest(fd,0,C.addressof(buffer),3,U128.from_int(END))
        receipt=ChunkReceipt(abi=1)
        function=self.receiver.library.jaydb_receiving_chunk_read_v1
        self.assertEqual(function(C.byref(request),C.byref(receipt)),0)
        self.assertEqual((receipt.state,receipt.received,bytes(buffer)),(2,3,b'abc'))
        self.assertEqual(function(C.byref(request),C.byref(receipt)),6)
        self.assertEqual((receipt.status,receipt.received),(0,3))
        self.assertEqual(os.read(fd,3),b'DEF')

    def test_native_chunk_expired_epoch_does_not_consume_bytes(self):
        fd=self.pipe(b'abc')
        buffer=C.create_string_buffer(3)
        request=ChunkRequest(fd,0,C.addressof(buffer),3,U128.from_int(time.monotonic_ns()))
        receipt=ChunkReceipt(abi=1)
        code=self.receiver.library.jaydb_receiving_chunk_read_v1(C.byref(request),C.byref(receipt))
        self.assertEqual((code,receipt.state,receipt.received),(4,2,0))
        self.assertGreaterEqual(receipt.started.integer(),request.deadline.integer())
        self.assertEqual(os.read(fd,3),b'abc')

    def test_native_raw_eintr_has_a_durable_zero_byte_result(self):
        r,w=os.pipe();self.fds.extend((r,w))
        buffer=C.create_string_buffer(3)
        request=ChunkRequest(r,0,C.addressof(buffer),3,U128.from_int(END))
        receipt=ChunkReceipt(abi=1)
        previous=signal.signal(signal.SIGUSR1,lambda *_:None)
        def interrupt():
            time.sleep(.02)
            os.kill(os.getpid(),signal.SIGUSR1)
        thread=threading.Thread(target=interrupt)
        thread.start()
        try:
            code=self.receiver.library.jaydb_receiving_chunk_read_v1(C.byref(request),C.byref(receipt))
        finally:
            signal.signal(signal.SIGUSR1,previous)
            thread.join()
        self.assertEqual((code,receipt.state,receipt.received,receipt.system_error),(2,2,0,errno.EINTR))
        os.write(w,b'abc')
        self.assertEqual(os.read(r,3),b'abc')

    def test_uncertain_native_chunk_blocks_library_close(self):
        self.receive((3).to_bytes(8,'big')+b'abc')
        owner=self.receiver._last_chunk
        self.receiver._chunk=owner
        owner.receipt.state=1 # explicit uncertain-state fixture, not a real running C call
        try:
            with self.assertRaisesRegex(IncompleteReceiving,'uncertain'):self.receiver.close()
            self.assertIsNotNone(self.receiver.library)
        finally:
            owner.receipt.state=2

    def test_prefix_copy_exception_keeps_committed_chunk_without_reread(self):
        fd=self.pipe((3).to_bytes(8,'big')+b'abc'+b'next')
        original=self.receiver._apply_chunk
        def after_copy(owner):
            original(owner)
            if owner.receipt.received==3:
                raise MemoryError('after receiving prefix was copied')
        with patch.object(self.receiver,'_apply_chunk',side_effect=after_copy):
            with self.assertRaisesRegex(MemoryError,'prefix was copied'):
                self.receiver.receive(fd,duration_ns=10**9,instrument_deadline_ns=END,
                    message_limit=100,memory_ceiling=100)
        self.assertEqual(bytes(self.receiver._read_prefix),b'abc')
        self.assertEqual(self.receiver.pending_chunk.data,b'abc')
        self.assertEqual(os.read(fd,4),b'next')
    def test_partial_header_is_preserved_on_eof(self):
        frame=self.receive(b'\0\0\3')
        self.assertEqual((frame.status,frame.close_channel,frame.header,frame.body),
            ('entrada',True,b'\0\0\3',b''))
    def test_partial_body_is_preserved_on_eof(self):
        header=(5).to_bytes(8,'big')
        frame=self.receive(header+b'ab')
        self.assertEqual((frame.status,frame.close_channel,frame.header,frame.body),
            ('entrada',True,header,b'ab'))
    def test_declared_excess_does_not_read_body(self):
        header=(101).to_bytes(8,'big')
        fd=self.pipe(header+b'unread')
        frame=self.receiver.receive(fd,duration_ns=1_000_000_000,
            instrument_deadline_ns=END,message_limit=100,memory_ceiling=100)
        self.assertEqual((frame.status,frame.body),('limite',b''))
        self.assertEqual(os.read(fd,6),b'unread')
    def test_header_wait_expires_without_renewing_epoch(self):
        frame=self.receive(b'\0',closed=False,duration=20_000_000)
        self.assertEqual((frame.status,frame.header),('limite',b'\0'))
        self.assertEqual(frame.start.deadline_ns,frame.start.started_ns+20_000_000)
        self.assertGreaterEqual(time.monotonic_ns(),frame.start.deadline_ns)
    def test_unbounded_nat_duration_has_no_float_or_decimal_quota(self):
        frame=self.receive((1).to_bytes(8,'big')+b'\xff',duration=10**5000)
        self.assertTrue(frame.complete)
        self.assertEqual(frame.body,b'\xff')
        self.assertEqual(frame.start.deadline_ns,2**128-1)
    def test_scope_must_close_before_next_first_byte(self):
        fd=self.pipe((1).to_bytes(8,'big')+b'A'+(1).to_bytes(8,'big')+b'B')
        options=dict(duration_ns=1_000_000_000,instrument_deadline_ns=END,
            message_limit=1,memory_ceiling=100)
        first=self.receiver.receive(fd,**options)
        with self.assertRaises(IncompleteReceiving):self.receiver.receive(fd,**options)
        self.lib.jaydb_receiving_test_peak(1000)
        self.lib.jaydb_receiving_test_close()
        second=self.receiver.receive(fd,**options)
        self.assertEqual((first.body,second.body),(b'A',b'B'))
        self.assertNotEqual(first.start.scope,second.start.scope)
        self.assertEqual(second.start.window.peak,100)
    def test_global_previous_peak_is_not_a_request_memory_witness(self):
        self.lib.jaydb_receiving_test_global_peak(10000)
        frame=self.receive((1).to_bytes(8,'big')+b'a',memory=100)
        self.assertTrue(frame.complete)
        self.assertGreater(frame.start.window.snapshot.peak,100)
        self.assertEqual(frame.start.window.peak,100)
    def test_incomplete_is_refused_even_for_numerical_excess(self):
        self.lib.jaydb_receiving_test_flags(3)
        with self.assertRaises(IncompleteReceiving):self.receive(bytes(8),memory=1)
        self.assertEqual(self.receiver.pending.window.snapshot.flags,3)
        self.assertTrue(self.counter.window_read().active)
    def test_cancelled_marker_has_no_invented_scope(self):
        self.lib.jaydb_receiving_test_error(errno.ETIMEDOUT)
        with self.assertRaises(IncompleteReceiving):self.receive(bytes(8))
        self.assertEqual(self.receiver.result.received,1)
        self.assertIsNone(self.receiver.pending)
        self.assertFalse(self.counter.window_read().active)
    def test_exception_at_ffi_return_preserves_first_byte_and_scope(self):
        previous=signal.signal(signal.SIGUSR1,lambda *_:(_ for _ in ()).throw(RuntimeError('after C')))
        self.lib.jaydb_receiving_test_signal(signal.SIGUSR1)
        try:
            with self.assertRaisesRegex(RuntimeError,'after C'):self.receive(b'Z')
        finally:signal.signal(signal.SIGUSR1,previous)
        receipt=self.receiver.pending
        self.assertEqual(receipt.byte,ord('Z'))
        self.assertEqual(receipt.scope,self.counter.window_read().scope_id)
        self.assertGreater(receipt.deadline_ns,receipt.started_ns)
    def test_loaded_fixture_cannot_be_enabled_by_report(self):
        with self.assertRaises(IncompleteReceiving):Receiver(self.path,self.counter)
        report_path=self.path.with_suffix('.so.json')
        report=json.loads(report_path.read_text());report['testFixture']=False
        report_path.write_text(json.dumps(report))
        with self.assertRaisesRegex(ValueError,'identity'):Receiver(self.path,self.counter)
    def test_idle_wait_is_outside_the_original_framing_epoch(self):
        r,w=os.pipe();self.fds.extend((r,w))
        written=[]
        def writer():
            time.sleep(.03)
            written.append(time.monotonic_ns())
            os.write(w,bytes(8))
        thread=threading.Thread(target=writer)
        thread.start()
        try:
            frame=self.receiver.receive(r,duration_ns=1_000_000_000,
                instrument_deadline_ns=END,message_limit=1,memory_ceiling=100)
        finally:thread.join()
        self.assertTrue(frame.complete)
        self.assertGreaterEqual(frame.start.started_ns,written[0])
        self.assertEqual(frame.start.deadline_ns-frame.start.started_ns,1_000_000_000)
    def test_local_excess_has_its_own_original_witness(self):
        original=self.counter.window_read
        def read():
            window=original()
            if window.active:
                self.lib.jaydb_receiving_test_peak(101)
                return original()
            return window
        self.counter.window_read=read
        frame=self.receive(bytes(8),memory=100)
        self.assertEqual(frame.status,'limite')
        self.assertEqual(frame.memory_excess.measured,101)
        self.assertEqual(frame.memory_excess.witness.scope_id,frame.start.scope)
        self.assertEqual(frame.memory_excess.witness.sequence,self.counter.window_read().peak_sequence)
    def test_cached_old_dso_is_not_authorized_by_a_new_report(self):
        build(self.path) # atomic rename, old fixture image remains mapped
        with self.assertRaisesRegex(ValueError,'identity'):Receiver(self.path,self.counter)
        self.assertEqual(self.receiver.library.jaydb_receiving_describe().contents.flags,1)
    def test_real_observer_refuses_incomplete_before_header_assembly(self):
        from tools.accounting.build import build as accounting_build
        output=Path(self.tmp.name)
        library,tracer=accounting_build(output/'accounting')
        production=output/'production.so'
        build(production)
        script=output/'real.py'
        script.write_text('''import json,os,sys
sys.path.insert(0,sys.argv[1])
from tools.accounting.client import Library,Counter
from tools.service.receiving import Receiver,IncompleteReceiving
library=Library(sys.argv[2])
counter=Counter(library,int(os.environ['JAYDB_ACCOUNTING_FD']))
receiver=Receiver(sys.argv[3],counter)
try:
  receiver.receive(0,duration_ns=10**30,instrument_deadline_ns=10**30,
    message_limit=100,memory_ceiling=1)
  raise AssertionError('INCOMPLETE became public permission')
except IncompleteReceiving:
  receipt=receiver.pending
  assert receipt and receipt.byte==0
  assert receipt.window.snapshot.flags&2
  assert counter.window_read().active
  assert os.read(0,7)==bytes(7)
library.window_end()
receiver.close();counter.close()
print(json.dumps({'incompleteRefused':True,'firstByteRetained':True,'restUnread':True}))
''')
        result=subprocess.run([str(tracer),'--report',str(output/'real.jsonl'),'--',
            sys.executable,'-B',str(script),str(ROOT),str(library),str(production)],
            input=bytes(8),capture_output=True,timeout=30)
        self.assertEqual(result.returncode,0,result.stderr.decode()+result.stdout.decode())
        self.assertEqual(json.loads(result.stdout),
            {'incompleteRefused':True,'firstByteRetained':True,'restUnread':True})
    def test_changed_scope_during_read_is_not_a_public_failure(self):
        original=self.counter.window_read
        def read():
            window=original()
            return replace(window,scope_id=window.scope_id+1) if window.active else window
        self.counter.window_read=read
        with self.assertRaises(IncompleteReceiving):self.receive(bytes(8))
        self.assertTrue(self.receiver.pending)
    def test_lost_coverage_during_read_is_not_a_public_failure(self):
        original=self.counter.window_read
        def read():
            window=original()
            return replace(window,snapshot=replace(window.snapshot,flags=3)) if window.active else window
        self.counter.window_read=read
        with self.assertRaises(IncompleteReceiving):self.receive(bytes(8))
        self.assertTrue(self.receiver.pending)

if __name__=='__main__':unittest.main()
