"""Experimental, retained-root binding for the bounded C commit primitive.

This is deliberately not wired into Database while allocation coverage remains
INCOMPLETE. It cannot turn a partial measurement into an authorized commit.
The C root is the source of truth after an exception at the ctypes return.
"""
from __future__ import annotations
import ctypes as C
import hashlib
import json
import mmap
from dataclasses import dataclass,field
from pathlib import Path

from tools.accounting.client import U128, NativeWindowSnapshot
from .frames import ERROR_FRAMES
from .loading import LibraryOwner
from .paired_loading import runtime_for

# Exact canonical frame of {status: "limite", valor: VAusente}. Prepared once,
# before a request's critical region. Its original Bend encoding is checked in
# proof/ErroLimiteFixo.bend; no formatting/allocation follows the barrier.
LIMIT_FRAME = ERROR_FRAMES['limite']


class NativePrepared(C.Structure):
    _fields_ = [('abi', C.c_uint64), ('publish', C.c_uint64),
                ('state', C.c_void_p), ('state_bytes', C.c_uint64),
                ('response', C.c_void_p), ('response_bytes', C.c_uint64)]


class NativeRoot(C.Structure):
    _fields_ = [('abi', C.c_uint64), ('published', C.c_void_p), ('completed', C.c_void_p)]


class NativeCommitResult(C.Structure):
    _fields_ = [('status', C.c_uint64), ('instrument_error', C.c_uint64),
                ('release_error', C.c_uint64), ('clock_error', C.c_uint64),
                ('window', NativeWindowSnapshot), ('checked_ns', U128)]


class NativeDescriptor(C.Structure):
    _fields_ = [(key,C.c_uint64) for key in ('abi','prepared_bytes','root_bytes',
                 'result_bytes','stack_bytes','flags')] + [('build_identity_sha256',C.c_char_p)]


class CommitFailure(RuntimeError):
    def __init__(self, result):
        self.result = result
        super().__init__(f'Commit refused: status={result.status}, instrument={result.instrument_error}')


def quantity(number):
    if type(number) is not int or number < 0:
        raise ValueError('Commit resources must be natural numbers')
    # The fixed host's aggregate addressable-capacity and clock domains fit in
    # u128. This clips a comparison bound, without reserving any backing.
    return U128.from_int(min(number, 2**128-1))


@dataclass(frozen=True,slots=True)
class PreparedView:
    abi:int
    publish:int
    state:int
    state_bytes:int
    response:int
    response_bytes:int


@dataclass(frozen=True,slots=True)
class RootView:
    abi:int
    published:int|None
    completed:int|None


@dataclass(frozen=True,slots=True,weakref_slot=True)
class Prepared:
    state:bytes
    response:bytes
    publish:bool
    limited:Prepared|None=None
    _state_owner:object=field(init=False,repr=False,compare=False)
    _response_owner:object=field(init=False,repr=False,compare=False)
    _record:object=field(init=False,repr=False,compare=False)
    _view:PreparedView=field(init=False,repr=False,compare=False)

    def __post_init__(self):
        if type(self.state) is not bytes or not self.state or type(self.response) is not bytes:
            raise ValueError('Prepared state/response must be immutable byte buffers')
        if type(self.publish) is not bool:
            raise ValueError('Prepared publication intent must be a boolean')
        # c_char_p holds the original immutable bytes, including embedded NUL;
        # the explicit extent is authoritative. No buffer copy is needed.
        state_owner,response_owner=C.c_char_p(self.state),C.c_char_p(self.response)
        record=NativePrepared(1,int(self.publish),C.cast(state_owner,C.c_void_p),len(self.state),
            C.cast(response_owner,C.c_void_p),len(self.response))
        object.__setattr__(self,'_state_owner',state_owner)
        object.__setattr__(self,'_response_owner',response_owner)
        object.__setattr__(self,'_record',record)
        object.__setattr__(self,'_view',PreparedView(*(getattr(record,key) for key,_ in NativePrepared._fields_)))

    @property
    def native(self):
        # Public inspection never exposes a writable ctypes record. The real
        # record and both byte owners are retained privately until teardown.
        return self._view

    def _check_seal(self):
        actual=PreparedView(*(getattr(self._record,key) for key,_ in NativePrepared._fields_))
        if actual!=self._view:
            raise ValueError('Prepared native record changed after its seal')

    @property
    def address(self):
        return C.addressof(self._record)


class Root:
    def __init__(self, library, initial_state, *, _test_fixture=False):
        self._closed=False
        self._finishing=False
        library = Path(library)
        report = json.loads(library.with_suffix(library.suffix+'.json').read_text())
        if hashlib.sha256(library.read_bytes()).hexdigest()!=report['moduleSha256']:
            raise ValueError('Commit module hash mismatch')
        if report['testFixture'] and not _test_fixture:
            raise ValueError('A unit-test fixture is not a production commit primitive')
        if not report['testFixture'] and not report['criticalFixedLoopsAndRawSyscallsOnly']:
            raise ValueError('Commit critical-body audit missing')
        self._library_owner=LibraryOwner.open(runtime_for(library,report),library)
        try:
            self._initialize(report,initial_state)
        except BaseException:
            try:
                stack=getattr(self,'stack',None)
                if stack is not None:stack.close()
            finally:
                self._library_owner.close()
            raise

    @property
    def library(self):
        return self._library_owner.library

    def _initialize(self, report, initial_state):
        describe=self.library.jaydb_commit_describe
        describe.argtypes,describe.restype=[],C.POINTER(NativeDescriptor)
        d=describe().contents
        if (d.abi!=1 or d.prepared_bytes!=C.sizeof(NativePrepared)
                or d.root_bytes!=C.sizeof(NativeRoot) or d.result_bytes!=C.sizeof(NativeCommitResult)
                or d.stack_bytes!=report['stackBytes'] or d.flags!=int(report['testFixture'])
                or not d.build_identity_sha256
                or d.build_identity_sha256.decode()!=report['buildIdentitySha256']):
            # dlopen may return an old DSO for a path that was rebuilt after
            # an earlier load. Hashing the file does not identify that mapping.
            raise ValueError('Loaded commit artifact differs from its pinned build descriptor')
        self.library.jaydb_commit_stack_bytes.argtypes = []
        self.library.jaydb_commit_stack_bytes.restype = C.c_uint64
        self.library.jaydb_commit_finish.argtypes = [C.POINTER(NativeRoot), C.POINTER(NativePrepared),
            U128, U128, U128, C.c_void_p, C.c_uint64, C.POINTER(NativeCommitResult)]
        self.library.jaydb_commit_finish.restype = C.c_uint64
        self.library.jaydb_commit_resolve.argtypes = [C.POINTER(NativeRoot), C.POINTER(NativePrepared),
            C.POINTER(NativePrepared), U128, U128, U128, U128, C.c_void_p,
            C.c_uint64, C.POINTER(NativeCommitResult)]
        self.library.jaydb_commit_resolve.restype = C.c_uint64
        self.stack_bytes = self.library.jaydb_commit_stack_bytes()
        if self.stack_bytes!=report['stackBytes'] or not self.stack_bytes or self.stack_bytes%4096:
            raise ValueError('Commit explicit-stack metadata mismatch')
        self.stack = mmap.mmap(-1, self.stack_bytes, flags=mmap.MAP_PRIVATE|mmap.MAP_ANONYMOUS,
                               prot=mmap.PROT_READ|mmap.PROT_WRITE)
        # Acquisition and activation precede every possible measurement/hold.
        self.stack[:] = b'\0'*self.stack_bytes
        self.stack_address = C.addressof(C.c_char.from_buffer(self.stack))
        initial = Prepared(initial_state,b'',False)
        self._records = {initial.address: initial}
        self._native = NativeRoot(1,initial.address,0)
        self._pending = None
        self.last_result = None

    @property
    def native(self):
        return RootView(self._native.abi,self._native.published,self._native.completed)

    def _require_open(self):
        if self._closed:
            raise RuntimeError('Request root is closed')

    @property
    def cleanup_complete(self):
        # Library consumption and stack release are independent resources.
        # Terminal API state alone does not authorize dropping their owner.
        return self._closed and self.stack.closed and self._library_owner.closed

    @property
    def state(self):
        self._require_open()
        prepared=self._records[self._native.published]
        prepared._check_seal()
        return prepared.state

    def prepare(self, response, *, state=None, with_limit=False):
        self._require_open()
        if self._pending is not None:
            raise RuntimeError('Only the serial request may own a pending finish')
        if type(response) is not bytes or not response:
            raise ValueError('A complete prepared response is required')
        old_state=self.state
        limited=Prepared(old_state,LIMIT_FRAME,False) if with_limit else None
        candidate=Prepared(old_state if state is None else state,response,state is not None,limited)
        # Construct the new owner set before replacing any owner. It retains
        # the published state, the latest completed response and this attempt,
        # including when an earlier FFI return raised after the C store.
        keep = {p:self._records[p] for p in (self.native.published,self.native.completed) if p}
        keep[candidate.address] = candidate
        if candidate.limited is not None:
            keep[candidate.limited.address] = candidate.limited
        self._records = keep
        self._pending = candidate
        return candidate

    def finish(self, prepared, *, scope, ceiling, deadline_ns):
        return self._finish(prepared,scope=scope,ceiling=ceiling,deadline_ns=deadline_ns)

    def finish_or_limit(self, prepared, *, scope, ceiling, deadline_ns, instrument_deadline_ns):
        return self._finish(prepared,scope=scope,ceiling=ceiling,deadline_ns=deadline_ns,
                            instrument_deadline_ns=instrument_deadline_ns)

    def _finish(self, prepared, *, scope, ceiling, deadline_ns, instrument_deadline_ns=None):
        self._require_open()
        if self._pending is not prepared:
            raise ValueError('Finish record does not belong to this serial request')
        try:
            # All fallible argument conversion and owner checks are inside the
            # same abort boundary, before native entry can possibly occur.
            scope,ceiling,deadline=U128.from_int(scope),quantity(ceiling),quantity(deadline_ns)
            result=NativeCommitResult()
            self.last_result=result
            prepared._check_seal()
            if self._records.get(prepared.address) is not prepared:
                raise ValueError('Prepared record has no retained owner')
            completed={prepared.address:prepared}
            if instrument_deadline_ns is not None:
                if prepared.limited is None:
                    raise ValueError('Fixed limite response must be prepared before entry')
                until=quantity(instrument_deadline_ns)
                limited=prepared.limited
                limited._check_seal()
                if (self._records.get(limited.address) is not limited or limited.publish
                        or limited.state is not self.state or limited.response is not LIMIT_FRAME):
                    raise ValueError('Limited record differs from its sealed retained alternative')
                completed[limited.address]=limited
            self._finishing=True
            try:
                if instrument_deadline_ns is None:
                    status = self.library.jaydb_commit_finish(C.byref(self._native),C.byref(prepared._record),
                        scope,ceiling,deadline,self.stack_address,self.stack_bytes,C.byref(result))
                else:
                    status = self.library.jaydb_commit_resolve(C.byref(self._native),C.byref(prepared._record),
                        C.byref(prepared.limited._record),scope,ceiling,deadline,until,
                        self.stack_address,self.stack_bytes,C.byref(result))
            except Exception:
                # CPython can dispatch a signal exception at a ctypes return,
                # after C has committed but before assigning status in Python.
                if self.native.completed in completed:
                    return completed[self.native.completed].response
                raise
            if self.native.completed in completed:
                return completed[self.native.completed].response
            if status!=result.status:
                raise RuntimeError('Commit result mismatch before completion')
            raise CommitFailure(result)
        finally:
            self._finishing=False
            self._pending = None

    def close(self):
        if self._finishing:
            raise RuntimeError('Cannot destroy a request root while C is executing')
        # A prepared-but-unsubmitted record is safe to abandon. A failed
        # pre-entry allocation must never prevent terminal cleanup.
        self._closed=True
        self._pending=None
        self._records.clear()
        self._native.published=None
        self._native.completed=None
        self.last_result=None
        failure=None
        try:self.stack.close()
        except BaseException as error:failure=error
        # The C close receipt is authoritative even when a handler raises at
        # the FFI return. A retry cannot consume this reference twice.
        try:self._library_owner.close()
        except BaseException as error:
            if failure is None:failure=error
        if failure is not None:raise failure
