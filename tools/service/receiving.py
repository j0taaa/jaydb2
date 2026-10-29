"""Private first-byte/framing integration, separate from the frozen CLI.

The native prefix opens the actual request scope before Python constructs the
header/body. Synthetic positive observations are test fixtures only. Real
INCOMPLETE observations never become public memory failures or permissions.
"""
from __future__ import annotations
import ctypes as C
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import select
import time

from tools.accounting.client import U128,NativeWindowSnapshot,WindowSnapshot
from .memory import MemoryWindow,MemoryExcess,validate
from .loading import LibraryOwner,LibraryScope
from .paired_loading import runtime_for


class IncompleteReceiving(Exception):
    """The selected environment has not discharged a receiving obligation."""


class NativeResult(C.Structure):
    _fields_=[*[(n,C.c_uint64) for n in ('abi','status','system_error','received','first_byte')],
        ('started_ns',U128),('received_ns',U128),('deadline_ns',U128),
        ('window',NativeWindowSnapshot)]


class Descriptor(C.Structure):
    _fields_=[('abi',C.c_uint64),('result_bytes',C.c_uint64),('flags',C.c_uint64),
        ('build_identity_sha256',C.c_char_p)]


class ChunkRequest(C.Structure):
    _fields_=[('fd',C.c_int32),('reserved',C.c_uint32),('buffer',C.c_void_p),
              ('quantity',C.c_uint64),('deadline',U128)]


class ChunkReceipt(C.Structure):
    _fields_=[('abi',C.c_uint32),('state',C.c_uint32),('status',C.c_uint32),
              ('system_error',C.c_uint32),('received',C.c_uint64),
              ('started',U128),('returned',U128)]


class ChunkDescriptor(C.Structure):
    _fields_=[('abi',C.c_uint64),('request_bytes',C.c_uint64),
              ('receipt_bytes',C.c_uint64),('flags',C.c_uint64),
              ('build_identity_sha256',C.c_char_p)]


assert C.sizeof(ChunkRequest)==40 and C.sizeof(ChunkReceipt)==56


@dataclass
class _Chunk:
    buffer: object
    request: ChunkRequest
    receipt: ChunkReceipt
    offset: int


@dataclass(frozen=True)
class ReceivedChunk:
    state:int
    status:int
    requested:int
    received:int
    data:bytes
    started_ns:int
    returned_ns:int
    deadline_ns:int


@dataclass(frozen=True)
class FirstByte:
    byte:int
    started_ns:int
    received_ns:int
    deadline_ns:int
    window:WindowSnapshot

    @property
    def scope(self):
        return self.window.scope_id


@dataclass(frozen=True)
class ReceivedFrame:
    start:FirstByte
    header:bytes
    body:bytes
    status:str|None
    close_channel:bool
    memory_excess:MemoryExcess|None=None
    error:OSError|None=None

    @property
    def complete(self):
        return self.status is None

    @property
    def framed(self):
        return len(self.header)==8 and int.from_bytes(self.header,'big')==len(self.body)


def _epoch(n,*,positive=False):
    if type(n) is not int or n<0 or (positive and not n):
        raise ValueError('An exact '+('positive ' if positive else '')+'Nat is required')
    # This target's CLOCK_MONOTONIC timespec domain is below 2**93 ns. Values
    # above the u128 representation all compare as unexpired in that domain.
    return U128.from_int(min(n,2**128-1))


class Receiver:
    def __init__(self,path,counter,*,allow_fixture=False,incomplete_type=IncompleteReceiving):
        self.counter=counter
        self.incomplete_type=incomplete_type
        self.result=NativeResult()
        self._chunk=None
        self._last_chunk=None
        self._read_prefix=None
        self._library_owner=None
        self._library_scope=LibraryScope()
        path=Path(path).resolve()
        report=json.loads(path.with_suffix(path.suffix+'.json').read_text())
        if hashlib.sha256(path.read_bytes()).hexdigest()!=report['moduleSha256']:
            raise ValueError('Receiving module hash mismatch')
        try:
            self._library_owner=LibraryOwner.open(runtime_for(path,report),path,scope=self._library_scope)
            lib=self.library
            describe=lib.jaydb_receiving_describe
            describe.argtypes,describe.restype=[],C.POINTER(Descriptor)
            d=describe().contents
            if (d.abi!=1 or d.result_bytes!=C.sizeof(NativeResult) or d.flags not in (0,1)
                    or d.flags!=int(report['testFixture'])
                    or d.build_identity_sha256.decode()!=report['buildIdentitySha256']):
                raise ValueError('Loaded receiving artifact does not match its identity')
            if d.flags and not allow_fixture:
                raise incomplete_type('A synthetic receiving fixture cannot enable the service')
            lib.jaydb_receiving_begin.argtypes=[C.c_int,U128,U128,C.POINTER(NativeResult)]
            lib.jaydb_receiving_begin.restype=C.c_uint64
            describe_chunk=lib.jaydb_receiving_chunk_describe_v1
            describe_chunk.argtypes=[]
            describe_chunk.restype=C.POINTER(ChunkDescriptor)
            chunk=describe_chunk().contents
            if (chunk.abi!=1 or chunk.request_bytes!=C.sizeof(ChunkRequest)
                    or chunk.receipt_bytes!=C.sizeof(ChunkReceipt) or chunk.flags!=d.flags
                    or report.get('chunkRequestBytes')!=40 or report.get('chunkReceiptBytes')!=56
                    or chunk.build_identity_sha256.decode()!=report['buildIdentitySha256']):
                raise ValueError('Loaded receiving chunk does not match its identity')
            lib.jaydb_receiving_chunk_read_v1.argtypes=[C.POINTER(ChunkRequest),C.POINTER(ChunkReceipt)]
            lib.jaydb_receiving_chunk_read_v1.restype=C.c_uint32
        except BaseException:
            self.close()
            raise

    def close(self):
        chunk=getattr(self,'_chunk',None)
        if chunk is not None and chunk.receipt.state==1:
            raise self.incomplete_type('A native read is still uncertain')
        scope=getattr(self,'_library_scope',None)
        if scope is None:
            # Cleanup can also see a partially initialized legacy receiver.
            owner=getattr(self,'_library_owner',None)
            if owner is not None:owner.close()
        else:
            for owner in scope.live_owners:
                owner.close()
            if scope.live_owners:
                raise self.incomplete_type('Receiving library ownership remains unresolved')
        self._chunk=self._last_chunk=self._read_prefix=None

    @property
    def library(self):
        owner=getattr(self,'_library_owner',None)
        return None if owner is None else owner.library

    @property
    def pending_chunk(self):
        owner=self._chunk if self._chunk is not None else self._last_chunk
        if owner is None:return None
        r,q=owner.receipt,owner.request
        if r.abi!=1 or r.state not in (0,1,2) or r.received>q.quantity:
            raise self.incomplete_type('Invalid durable receiving chunk')
        return ReceivedChunk(r.state,r.status,q.quantity,r.received,
            bytes(owner.buffer[:r.received]),r.started.integer(),r.returned.integer(),
            q.deadline.integer())

    def _apply_chunk(self,owner):
        r=owner.receipt
        data=self._read_prefix
        if (r.abi!=1 or r.state!=2 or r.status>5 or r.received>owner.request.quantity
                or data is None):
            raise self.incomplete_type('Native read has no complete durable outcome')
        chunk=bytes(owner.buffer[:r.received])
        if len(data)==owner.offset:
            data.extend(chunk)
        elif len(data)!=owner.offset+r.received or data[owner.offset:]!=chunk:
            raise self.incomplete_type('Receiving prefix and durable read disagree')
        # If Python throws after extend but before these assignments, the
        # offset/length check above prevents applying the same bytes twice.
        self._last_chunk=owner
        self._chunk=None

    @property
    def pending(self):
        """A retained receipt is observable even after an FFI return exception.

        Coverage remains visible in its flags. Reading this property does not
        authorize processing or silently close/reopen the scope.
        """
        r=self.result
        if r.received!=1 or r.window.abi!=1 or r.window.state!=1 or r.window.error:
            return None
        return FirstByte(r.first_byte,r.started_ns.integer(),r.received_ns.integer(),
            r.deadline_ns.integer(),WindowSnapshot.native(r.window))

    def begin(self,fd,*,duration_ns,instrument_deadline_ns):
        if self.library is None:
            raise RuntimeError('Receiver closed')
        if type(fd) is not int or not 0<=fd<2**31:
            raise ValueError('Invalid Linux file descriptor')
        duration=_epoch(duration_ns,positive=True)
        instrument=_epoch(instrument_deadline_ns,positive=True)
        try:
            active=self.counter.window_read().active
        except Exception as exc:
            raise self.incomplete_type('Receiving counter is unavailable') from exc
        if active:
            raise self.incomplete_type('Initialization/previous request must close its scope before receiving')
        self.result=NativeResult() # acquired before waiting for a first byte
        code=self.library.jaydb_receiving_begin(fd,duration,instrument,C.byref(self.result))
        r=self.result
        if code!=r.status or r.abi!=1:
            raise self.incomplete_type('Invalid receiving result')
        if code==1:
            if r.received or r.window.abi:
                raise self.incomplete_type('EOF between messages cannot open a request')
            return None
        if code==2:
            raise InterruptedError(r.system_error,'Receiving interrupted between messages')
        if code==3:
            raise OSError(r.system_error,'Native receiving operation failed')
        if code in (4,5,6):
            raise self.incomplete_type('Receiving scope/instrument coverage is unavailable')
        start=self.pending
        if (code!=0 or start is None or not 0<=start.byte<=255
                or not 0<start.started_ns<=start.received_ns
                or start.received_ns>start.window.begin_monotonic_ns
                or start.deadline_ns<=start.started_ns):
            raise self.incomplete_type('Receiving first-byte provenance is inconsistent')
        try:
            validate(start.window,start.scope)
        except Exception as exc:
            raise self.incomplete_type('Receiving requires the exact complete request scope') from exc
        return start

    def _poll(self,monitor):
        try:
            return monitor.poll()
        except MemoryExcess:
            raise
        except Exception as exc:
            raise self.incomplete_type('Receiving scope lost complete coverage/provenance') from exc

    def _read(self,fd,size,deadline,monitor):
        """Return every received byte, including prefixes on EOF/time/failure."""
        if self._chunk is not None:
            raise self.incomplete_type('An earlier native read remains unresolved')
        data=bytearray()
        self._read_prefix=data
        while len(data)<size:
            try:
                self._poll(monitor)
            except MemoryExcess as excess:
                return bytes(data),False,'limite',excess,None
            left=deadline-time.monotonic_ns()
            if left<=0:
                return bytes(data),False,'limite',None,None
            try:
                ready,_,_=select.select([fd],[],[],min(left,10_000_000)/1_000_000_000)
                if not ready:
                    continue
            except OSError as error:
                return bytes(data),False,'falha',None,error
            quantity=min(size-len(data),65536)
            buffer=C.create_string_buffer(quantity)
            owner=_Chunk(buffer,ChunkRequest(fd,0,C.addressof(buffer),quantity,_epoch(deadline)),
                         ChunkReceipt(abi=1),len(data))
            self._chunk=owner # before the actual read, including FFI return exceptions
            error=None
            try:
                code=self.library.jaydb_receiving_chunk_read_v1(C.byref(owner.request),C.byref(owner.receipt))
            except OSError as caught:
                error=caught
                code=None
            if code is not None and code!=owner.receipt.status:
                raise self.incomplete_type('Receiving chunk return disagrees with its receipt')
            self._apply_chunk(owner)
            full=len(data)==size
            if error is not None:
                return bytes(data),full,'falha',None,error
            if owner.receipt.status==2: # raw EINTR, durably zero consumed bytes
                if owner.receipt.received:
                    raise self.incomplete_type('Interrupted raw read reported consumed bytes')
                continue
            if owner.receipt.status==3:
                error=OSError(owner.receipt.system_error,'Native receiving read failed')
                return bytes(data),full,'falha',None,error
            if owner.receipt.status==4:
                return bytes(data),full,'limite',None,None
            if owner.receipt.status==5:
                raise self.incomplete_type('Native receiving read rejected its host arguments')
            if owner.receipt.status==1:
                return bytes(data),False,'entrada',None,None
            if not owner.receipt.received:
                raise self.incomplete_type('Successful native read made no progress')
        try:
            self._poll(monitor)
        except MemoryExcess as excess:
            return bytes(data),True,'limite',excess,None
        if time.monotonic_ns()>=deadline:
            return bytes(data),True,'limite',None,None
        return bytes(data),True,None,None,None

    def receive(self,fd,*,duration_ns,instrument_deadline_ns,message_limit,memory_ceiling):
        if type(message_limit) is not int or not 0<=message_limit<2**64:
            raise ValueError('Message byte limit must fit the original u64 domain')
        if type(memory_ceiling) is not int or memory_ceiling<=0:
            raise ValueError('Memory ceiling must be a positive Nat')
        start=self.begin(fd,duration_ns=duration_ns,instrument_deadline_ns=instrument_deadline_ns)
        if start is None:
            return None
        monitor=MemoryWindow(self.counter,start.scope,memory_ceiling)
        tail,complete,status,witness,error=self._read(fd,7,start.deadline_ns,monitor)
        header=bytes([start.byte])+tail
        if status is not None or not complete:
            framed=len(header)==8 and int.from_bytes(header,'big')==0
            return ReceivedFrame(start,header,b'',status or 'entrada',not framed,witness,error)
        size=int.from_bytes(header,'big')
        if size>message_limit:
            return ReceivedFrame(start,header,b'','limite',True)
        body,complete,status,witness,error=self._read(fd,size,start.deadline_ns,monitor)
        return ReceivedFrame(start,header,body,status,not complete,witness,error)
