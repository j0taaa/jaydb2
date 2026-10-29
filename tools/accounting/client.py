"""Native allocation-counter bindings; no claim of a complete MedicaoReal.

The shared counter is u128. Public ceilings remain arbitrary Python integers.
A barrier returns an immutable observation from its stopped-world instant.
Reading a shared counter without a barrier returns the last published instant,
not a continuously current measurement while tracees are running.
"""
from __future__ import annotations
import ctypes as C
from dataclasses import dataclass
import errno
import mmap
import os
from pathlib import Path

FROZEN = 1
INCOMPLETE = 2
OWNER_DIED = 4
SHARED_BYTES = 4096


class U128(C.Structure):
    _fields_ = [('lo', C.c_uint64), ('hi', C.c_uint64)]

    @classmethod
    def from_int(cls, n):
        if type(n) is not int or not 0 <= n < 2**128:
            raise ValueError('Counter quantity must be a uint128')
        return cls(n & (2**64 - 1), n >> 64)

    def integer(self):
        return self.lo + (self.hi << 64)


class NativeSnapshot(C.Structure):
    _fields_ = [('abi', C.c_uint64), ('sequence', U128),
                ('current', U128), ('peak', U128),
                ('monotonic_ns', U128), ('peak_monotonic_ns', U128),
                ('peak_sequence', U128), ('peak_flags', C.c_uint64), ('flags', C.c_uint64)]


class NativeWindowSnapshot(C.Structure):
    _fields_ = [('abi', C.c_uint64), ('state', C.c_uint64), ('error', C.c_uint64),
                ('snapshot', NativeSnapshot), ('scope_id', U128), ('begin_sequence', U128),
                ('begin_monotonic_ns', U128), ('end_sequence', U128), ('end_monotonic_ns', U128),
                ('peak', U128), ('peak_monotonic_ns', U128), ('peak_sequence', U128),
                ('peak_flags', C.c_uint64)]


@dataclass(frozen=True)
class Snapshot:
    sequence: int
    current: int
    peak: int
    monotonic_ns: int
    peak_monotonic_ns: int
    peak_sequence: int
    peak_flags: int
    flags: int

    @classmethod
    def native(cls, n):
        if n.abi != 1:
            raise ValueError('Unknown allocation-counter ABI')
        return cls(n.sequence.integer(), n.current.integer(), n.peak.integer(),
                   n.monotonic_ns.integer(), n.peak_monotonic_ns.integer(),
                   n.peak_sequence.integer(), n.peak_flags, n.flags)

    def exceeds(self, ceiling):
        if type(ceiling) is not int or ceiling < 0:
            raise ValueError('Public ceiling must be a Nat')
        return self.current > ceiling

    def require_complete(self):
        if not self.sequence or self.flags & (INCOMPLETE | OWNER_DIED):
            raise IncompleteCoverage('Allocation snapshot has explicit unresolved coverage obligations')
        return self

    def excess_witness(self, ceiling):
        """A historical observation, with its original time, or None.

        This preserves provenance; it does not discharge coverage or produce
        MedicaoReal. Current and historical peak are distinct observations.
        """
        if self.exceeds(ceiling):
            return Witness(self.current, self.sequence, self.monotonic_ns, self.flags)
        if self.peak > ceiling and self.peak_sequence:
            return Witness(self.peak, self.peak_sequence, self.peak_monotonic_ns, self.peak_flags)
        return None


@dataclass(frozen=True)
class Witness:
    amount: int
    sequence: int
    monotonic_ns: int
    flags: int


@dataclass(frozen=True)
class WindowWitness(Witness):
    scope_id: int
    begin_sequence: int
    end_sequence: int


@dataclass(frozen=True)
class WindowSnapshot:
    snapshot: Snapshot
    scope_id: int
    state: int
    begin_sequence: int
    begin_monotonic_ns: int
    end_sequence: int
    end_monotonic_ns: int
    peak: int
    peak_monotonic_ns: int
    peak_sequence: int
    peak_flags: int

    @classmethod
    def native(cls, n):
        if n.abi != 1:
            raise ValueError('Unknown allocation-window ABI')
        _check(n.error)
        return cls(Snapshot.native(n.snapshot), n.scope_id.integer(), n.state,
                   n.begin_sequence.integer(), n.begin_monotonic_ns.integer(),
                   n.end_sequence.integer(), n.end_monotonic_ns.integer(),
                   n.peak.integer(), n.peak_monotonic_ns.integer(),
                   n.peak_sequence.integer(), n.peak_flags)

    @property
    def active(self):
        return self.state == 1

    def require_scope(self, scope_id):
        if not self.scope_id or self.scope_id != scope_id:
            raise ValueError('Allocation window identity changed')
        return self

    def require_complete(self):
        self.snapshot.require_complete()
        if not self.scope_id or self.peak_flags & (INCOMPLETE | OWNER_DIED):
            raise IncompleteCoverage('Allocation window has unresolved coverage obligations')
        return self

    def excess_witness(self, ceiling):
        # Never fall back to the global peak, including after this scope closes.
        if type(ceiling) is not int or ceiling < 0:
            raise ValueError('Public ceiling must be a Nat')
        if self.scope_id and self.peak > ceiling and self.peak_sequence:
            return WindowWitness(self.peak, self.peak_sequence, self.peak_monotonic_ns, self.peak_flags,
                                 self.scope_id, self.begin_sequence, self.end_sequence)
        return None


class IncompleteCoverage(RuntimeError):
    pass


def _check(code):
    if code:
        raise OSError(code, os.strerror(code))


class Library:
    def __init__(self, path):
        self.path = Path(path)
        self.native = C.CDLL(str(self.path))
        self.native.jayacct_init.argtypes = [C.c_void_p, C.c_size_t]
        self.native.jayacct_change.argtypes = [C.c_void_p, U128, U128, C.POINTER(NativeSnapshot)]
        self.native.jayacct_publish.argtypes = [C.c_void_p, U128, C.c_uint64, C.POINTER(NativeSnapshot)]
        self.native.jayacct_read.argtypes = [C.c_void_p, C.POINTER(NativeSnapshot)]
        for name in ('jayacct_window_open', 'jayacct_window_close', 'jayacct_window_read'):
            getattr(self.native, name).argtypes = [C.c_void_p, C.POINTER(NativeWindowSnapshot)]
            getattr(self.native, name).restype = C.c_int
        for name in ('jayacct_window_begin', 'jayacct_window_end', 'jayacct_window_barrier'):
            getattr(self.native, name).argtypes = [C.POINTER(NativeWindowSnapshot)]
            getattr(self.native, name).restype = C.c_int
        for name in ('jayacct_barrier', 'jayacct_hold_begin', 'jayacct_hold_end'):
            getattr(self.native, name).argtypes = [C.POINTER(NativeSnapshot)]
        for name in ('jayacct_barrier_until', 'jayacct_hold_begin_until', 'jayacct_hold_end_until'):
            getattr(self.native, name).argtypes = [C.POINTER(NativeSnapshot), U128]
            getattr(self.native, name).restype = C.c_int
        for name in ('jayacct_window_begin_until', 'jayacct_window_end_until', 'jayacct_window_barrier_until'):
            getattr(self.native, name).argtypes = [C.POINTER(NativeWindowSnapshot), U128]
            getattr(self.native, name).restype = C.c_int
        self.native.jayacct_hold_release.argtypes = []
        self.native.jayacct_hold_release.restype = C.c_int
        for name in ('jayacct_init', 'jayacct_change', 'jayacct_publish', 'jayacct_read',
                     'jayacct_barrier', 'jayacct_hold_begin', 'jayacct_hold_end'):
            getattr(self.native, name).restype = C.c_int

    def barrier(self):
        n = NativeSnapshot()
        _check(self.native.jayacct_barrier(C.byref(n)))
        return Snapshot.native(n)

    def hold_begin(self):
        n = NativeSnapshot()
        _check(self.native.jayacct_hold_begin(C.byref(n)))
        return Snapshot.native(n)

    def hold_end(self):
        n = NativeSnapshot()
        _check(self.native.jayacct_hold_end(C.byref(n)))
        return Snapshot.native(n)

    def _window_marker(self, name):
        n = NativeWindowSnapshot()
        _check(getattr(self.native, name)(C.byref(n)))
        return WindowSnapshot.native(n)

    def window_begin(self):
        return self._window_marker('jayacct_window_begin')

    def window_end(self):
        return self._window_marker('jayacct_window_end')

    def window_barrier(self):
        return self._window_marker('jayacct_window_barrier')

    def _until(self, name, deadline, window=False):
        n = NativeWindowSnapshot() if window else NativeSnapshot()
        _check(getattr(self.native, name)(C.byref(n), U128.from_int(deadline)))
        return WindowSnapshot.native(n) if window else Snapshot.native(n)

    def barrier_until(self, deadline):
        return self._until('jayacct_barrier_until', deadline)

    def hold_begin_until(self, deadline):
        return self._until('jayacct_hold_begin_until', deadline)

    def hold_end_until(self, deadline):
        return self._until('jayacct_hold_end_until', deadline)

    def window_begin_until(self, deadline):
        return self._until('jayacct_window_begin_until', deadline, True)

    def window_end_until(self, deadline):
        return self._until('jayacct_window_end_until', deadline, True)

    def window_barrier_until(self, deadline):
        return self._until('jayacct_window_barrier_until', deadline, True)

    def hold_release(self):
        _check(self.native.jayacct_hold_release())


class Counter:
    """Cooperative ledger. Does not automatically instrument its Python owner.

    Neither construction nor attach adds an implicit charge: the adapter owns
    and must register the page exactly once, along with its own backing. An
    attached inherited fd references the same object, rather than a fresh one.
    The native tracer instead discovers the page and deduplicates its aliases.
    """
    def __init__(self, library, fd=None, *, initialize=None):
        self.library = library
        created = fd is None
        self.fd = os.memfd_create('jaydb-cooperative-counter', 0) if created else os.dup(fd)
        if created:
            os.ftruncate(self.fd, SHARED_BYTES)
        self.mapping = mmap.mmap(self.fd, SHARED_BYTES, flags=mmap.MAP_SHARED,
                                 prot=mmap.PROT_READ | mmap.PROT_WRITE)
        self.address = C.addressof(C.c_char.from_buffer(self.mapping))
        if initialize is True or (initialize is None and created):
            _check(library.native.jayacct_init(self.address, SHARED_BYTES))

    def change(self, *, acquired=0, released=0):
        n = NativeSnapshot()
        _check(self.library.native.jayacct_change(self.address, U128.from_int(released),
                                                 U128.from_int(acquired), C.byref(n)))
        return Snapshot.native(n)

    def read(self):
        n = NativeSnapshot()
        _check(self.library.native.jayacct_read(self.address, C.byref(n)))
        return Snapshot.native(n)

    def window_read(self):
        n = NativeWindowSnapshot()
        _check(self.library.native.jayacct_window_read(self.address, C.byref(n)))
        return WindowSnapshot.native(n)

    def close(self):
        self.mapping.close()
        os.close(self.fd)
