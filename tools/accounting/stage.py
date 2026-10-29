"""Opt-in original-stage deadline control, ABI1. No memory/coverage claim.

The observer creates the control page before its baseline. Helpers are observed
by PID and need no access to this FD. Expiry is PENDING until real reconciliation;
window ACTIVE is never reinterpreted as CLOSED by any operation here.
"""
from __future__ import annotations
import ctypes as C
from dataclasses import dataclass
import os
from .client import U128, _check

IDLE, ARMED, EXPIRED_PENDING_RECOVERY, EXPIRED_RECOVERED, RETIRED = range(5)

class NativeRequest(C.Structure):
    _fields_ = [('abi', C.c_uint64), ('stage', C.c_uint64),
                ('scope_id', U128), ('generation', U128), ('start_ns', U128), ('deadline_ns', U128)]

class NativeReceipt(C.Structure):
    _fields_ = [('abi', C.c_uint64), ('error', C.c_uint64), ('state', C.c_uint64), ('stage', C.c_uint64),
                *[(name, U128) for name in ('scope_id', 'generation', 'start_ns', 'deadline_ns',
                                          'observed_ns', 'arm_sequence', 'recovery_sequence')],
                *[(name, C.c_uint64) for name in ('owner_pid', 'owner_mm', 'pending_flags', 'cancellations')]]

@dataclass(frozen=True)
class Request:
    scope_id: int
    generation: int
    stage: int
    start_ns: int
    deadline_ns: int

    def native(self):
        if type(self.stage) is not int or not 0 < self.stage < 2**64:
            raise ValueError('Stage identity must be a nonzero uint64')
        return NativeRequest(1, self.stage, *[U128.from_int(v) for v in
                            (self.scope_id, self.generation, self.start_ns, self.deadline_ns)])

@dataclass(frozen=True)
class Receipt:
    state: int
    stage: int
    scope_id: int
    generation: int
    start_ns: int
    deadline_ns: int
    observed_ns: int
    arm_sequence: int
    recovery_sequence: int
    owner_pid: int
    owner_mm: int
    pending_flags: int
    cancellations: int

    @classmethod
    def native(cls, n):
        if n.abi != 1:
            raise ValueError('Unknown stage-control ABI')
        _check(n.error)
        return cls(*[getattr(n, name).integer() if isinstance(getattr(n, name), U128)
                     else getattr(n, name) for name in cls.__dataclass_fields__])

class StageControl:
    def __init__(self, library, fd=None):
        self.library = library
        self.fd = os.dup(int(os.environ['JAYDB_ACCOUNTING_STAGE_FD']) if fd is None else fd)
        self.page = C.c_void_p()
        lib = library.native
        for name in ('jaystage_arm', 'jaystage_retire'):
            getattr(lib, name).argtypes = [C.POINTER(NativeRequest), C.POINTER(NativeReceipt)]
            getattr(lib, name).restype = C.c_int
        lib.jaystage_read.argtypes = [C.c_void_p, C.POINTER(NativeReceipt)]
        lib.jaystage_read.restype = C.c_int
        lib.jaystage_map.argtypes = [C.c_int, C.POINTER(C.c_void_p)]
        lib.jaystage_map.restype = C.c_int
        lib.jaystage_unmap.argtypes = [C.c_void_p]
        lib.jaystage_unmap.restype = C.c_int
        try:
            _check(lib.jaystage_map(self.fd, C.byref(self.page)))
        except BaseException:
            os.close(self.fd)
            raise

    def _call(self, name, request):
        n = request.native()
        out = NativeReceipt()
        _check(getattr(self.library.native, name)(C.byref(n), C.byref(out)))
        return Receipt.native(out)

    def arm(self, request):
        return self._call('jaystage_arm', request)

    def retire(self, request):
        return self._call('jaystage_retire', request)

    def read(self):
        n = NativeReceipt()
        _check(self.library.native.jaystage_read(self.page, C.byref(n)))
        return Receipt.native(n)

    def close(self):
        if self.page.value:
            _check(self.library.native.jaystage_unmap(self.page))
            self.page.value = None
        if self.fd >= 0:
            os.close(self.fd)
            self.fd = -1
