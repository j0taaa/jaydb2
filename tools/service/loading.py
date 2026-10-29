"""Explicit loader installation and receipt-owned dlopen references (Linux ABI 1).

Host API::

    manifest = build_loading.build(path)       # offline / installation only
    runtime = Runtime.load(path, manifest=manifest)
    owner = LibraryOwner.open(runtime, target_path)
    library = owner.library                    # ctypes.CDLL, no extra reference
    owner.close()                              # idempotent after C success

One fixed shim is retained for the process lifetime, including its initial
dlopen reference. Both RTLD_NODELETE and the linker's NODELETE flag keep the shim
mapped while its FFI calls return. Installation is explicit. This retention is
an ownership requirement; the active service has no physical-memory budget.

Bootstrap precedes availability of our receipt API. Its one attempt is reserved
in the process singleton BEFORE ctypes loads it. An exceptional bootstrap poisons
the slot: no retry/new installation can accumulate lost bootstrap references.
The OS releases this deliberately retained baseline. Normal repeated load calls
reuse the verified runtime without another dlopen. A different identity requires
a new process. No request compiles, installs, replaces, or unloads this runtime.

Owners are retained by the runtime until close is durably recorded, including
setup failures and exceptions at FFI return. Callers may inspect live_owners to
recover such ownership. library is None exactly when the C close receipt records
success; Python assignment is not the release event. Uncertain operations refuse
retry. This does not make function pointers safe to use concurrently with close,
nor recover C non-local exits, asynchronous thread cancellation, or process death.
The host must finish all calls/leases before closing a target reference.
"""
from __future__ import annotations

import ctypes as C
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import re
import threading

ABI = 1
OK, DL_ERROR, BAD_ABI, UNCERTAIN, NOT_OPEN = range(5)


class LoadingError(RuntimeError):
    pass


class IdentityMismatch(ValueError):
    pass


class InstallationError(LoadingError):
    pass


class UncertainOperation(LoadingError):
    pass


class OpenError(LoadingError):
    pass


class CloseError(LoadingError):
    pass


class _OpenReceipt(C.Structure):
    _fields_ = [('abi', C.c_uint32), ('entered', C.c_uint32),
                ('outcome', C.c_uint64), ('handle', C.c_void_p)]


class _CloseReceipt(C.Structure):
    _fields_ = [('abi', C.c_uint32), ('entered', C.c_uint32), ('outcome', C.c_uint64)]


class _Descriptor(C.Structure):
    _fields_ = [('abi', C.c_uint32), ('size', C.c_uint32),
                ('open_receipt_bytes', C.c_uint32), ('close_receipt_bytes', C.c_uint32),
                ('pointer_bytes', C.c_uint32), ('reserved', C.c_uint32),
                ('flags', C.c_uint64), ('build_identity', C.c_char * 64)]


assert C.sizeof(_OpenReceipt) == 24 and _OpenReceipt.outcome.offset == 8
assert C.sizeof(_CloseReceipt) == 16 and _CloseReceipt.outcome.offset == 8
assert C.sizeof(_Descriptor) == 96 and C.sizeof(C.c_void_p) == 8


@dataclass(frozen=True)
class Receipt:
    abi: int
    entered: bool
    returned: bool
    status: int
    handle: int | None = None


@dataclass(frozen=True)
class RuntimeIdentity:
    abi: int
    build_identity_sha256: str
    module_sha256: str
    baseline_retention: str = 'process lifetime; one fixed NODELETE runtime'


def _receipt(native):
    # One aligned scalar load of the C atomic pair: never combine the returned
    # bit of one close attempt with the status of a different attempt.
    outcome = native.outcome
    return Receipt(native.abi, bool(native.entered), bool(outcome & 0xffffffff),
                   C.c_int32(outcome >> 32).value, getattr(native, 'handle', None))


def _closed(native):
    return native.abi == ABI and bool(native.entered) and native.outcome == 1


_installation = None
_installation_lock = threading.RLock()


def _read_manifest(path, manifest):
    if manifest is None:
        manifest = json.loads(path.with_suffix(path.suffix+'.json').read_text())
    elif isinstance(manifest, (str, os.PathLike)):
        manifest = json.loads(Path(manifest).read_text())
    # Copy only the pinned fields, never retain the caller's mutable dictionary.
    expected = {'abiVersion': ABI, 'descriptorBytes': C.sizeof(_Descriptor),
                'openReceiptBytes': C.sizeof(_OpenReceipt),
                'closeReceiptBytes': C.sizeof(_CloseReceipt), 'pointerBytes': 8,
                'nodelete': True}
    if any(type(manifest.get(key)) is not type(value) or manifest[key] != value
           for key, value in expected.items()):
        raise IdentityMismatch('Loading manifest ABI/layout/NODELETE mismatch')
    for key in ('moduleSha256', 'buildIdentitySha256'):
        if not isinstance(manifest.get(key), str) or not re.fullmatch('[0-9a-f]{64}', manifest[key]):
            raise IdentityMismatch('Loading manifest lacks a pinned '+key)
    identity = RuntimeIdentity(ABI, manifest['buildIdentitySha256'], manifest['moduleSha256'])
    if hashlib.sha256(path.read_bytes()).hexdigest() != identity.module_sha256:
        raise IdentityMismatch('Loading binary hash does not match manifest')
    return identity


def _absolute_path(path):
    # Do not resolve symlinks: /proc/self/fd/N may name an already unlinked DSO
    # or memfd. Its readlink target is not necessarily an openable pathname.
    return Path(os.path.abspath(os.fsdecode(os.fspath(path))))


class Runtime:
    """Process singleton. Use load(); there is deliberately no close/uninstall."""
    __slots__ = ('_identity', '_path', '_state', '_shim', '_owners', '_open', '_close')

    def __init__(self):
        raise TypeError('Use Runtime.load(path, manifest=...) explicitly')

    @classmethod
    def current(cls):
        """Return the explicitly installed runtime; never build or load one."""
        with _installation_lock:
            if _installation is None or _installation._state != 'ready':
                raise InstallationError('Install the fixed loading runtime before starting the service')
            return _installation

    @classmethod
    def load(cls, path, *, manifest=None):
        global _installation
        path = _absolute_path(path)
        identity = _read_manifest(path, manifest)
        with _installation_lock:
            if _installation is not None:
                if _installation.identity != identity:
                    raise IdentityMismatch('Loading runtime identity is fixed for this process')
                if _installation._state != 'ready':
                    raise InstallationError('Previous bootstrap is uncertain/failed; restart the process')
                return _installation
            runtime = object.__new__(cls)
            runtime._identity = identity
            runtime._path = path
            runtime._state = 'loading'
            runtime._shim = None
            runtime._owners = set()
            # Reserve the only bootstrap attempt before anything can acquire a
            # reference. Exceptions do not open a path to repeated hidden loads.
            _installation = runtime
            try:
                runtime._install()
                runtime._state = 'ready'
                return runtime
            except BaseException:
                runtime._state = 'failed'
                raise

    @property
    def identity(self):
        return self._identity

    @property
    def path(self):
        return self._path

    def _install(self):
        self._shim = C.CDLL(str(self.path), mode=os.RTLD_NOW | os.RTLD_LOCAL | os.RTLD_NODELETE)
        describe = self._shim.jaydb_loading_describe_v1
        describe.argtypes = []
        describe.restype = C.POINTER(_Descriptor)
        pointer = describe()
        if not pointer:
            raise IdentityMismatch('Loaded loading descriptor is absent')
        descriptor = pointer.contents
        expected = (ABI, C.sizeof(_Descriptor), C.sizeof(_OpenReceipt),
                    C.sizeof(_CloseReceipt), 8, 0, 1)
        actual = tuple(getattr(descriptor, key) for key in
                       ('abi', 'size', 'open_receipt_bytes', 'close_receipt_bytes',
                        'pointer_bytes', 'reserved', 'flags'))
        if actual != expected or bytes(descriptor.build_identity) != \
                self.identity.build_identity_sha256.encode('ascii'):
            raise IdentityMismatch('Loaded loading descriptor/identity does not match manifest')
        # Recheck disk identity after dlopen, too. Compiled identity above rejects
        # an older mapping returned by dlopen's path cache after atomic rebuild.
        if hashlib.sha256(self.path.read_bytes()).hexdigest() != self.identity.module_sha256:
            raise IdentityMismatch('Loading binary changed during installation')
        self._open = self._shim.jaydb_loading_open_v1
        self._open.argtypes = [C.c_char_p, C.c_int, C.POINTER(_OpenReceipt)]
        self._open.restype = C.c_int
        self._close = self._shim.jaydb_loading_close_v1
        self._close.argtypes = [C.POINTER(_OpenReceipt), C.POINTER(_CloseReceipt)]
        self._close.restype = C.c_int

    @property
    def live_owners(self):
        """Strongly retained live/uncertain owners, including exceptional setup."""
        for owner in tuple(self._owners):
            self._retire(owner)
        return tuple(self._owners)

    def _retire(self, owner):
        opened = owner.open_receipt
        if owner.closed or (opened.returned and opened.status != 0) or \
                (not opened.entered and not owner._opening):
            self._owners.discard(owner)
            if owner.closed:
                owner._library = None  # merely drops Python wrappers; C receipt is authority


class LibraryOwner:
    """One acquired reference. No __del__: runtime keeps unresolved owners alive."""
    __slots__ = ('_runtime', '_path', '_opened', '_closed', '_library', '_opening', '__weakref__')

    def __init__(self):
        raise TypeError('Use LibraryOwner.open(runtime, path)')

    @classmethod
    def open(cls, runtime, path, *, scope=None):
        if not isinstance(runtime, Runtime) or runtime._state != 'ready':
            raise InstallationError('An explicitly installed loading runtime is required')
        path = os.fsencode(_absolute_path(path))
        if b'\0' in path:
            raise ValueError('Library path contains NUL')
        owner = object.__new__(cls)
        owner._runtime = runtime
        owner._path = path
        owner._opened = _OpenReceipt(abi=ABI)
        owner._closed = _CloseReceipt(abi=ABI)
        owner._library = None
        owner._opening = True
        try:
            if scope is not None:
                scope._owners.add(owner)  # request identity, BEFORE acquisition/return assignment
            runtime._owners.add(owner)   # ownership is armed BEFORE dlopen
            result = runtime._open(path, os.RTLD_NOW | os.RTLD_LOCAL, C.byref(owner._opened))
            opened = owner.open_receipt
            if opened.entered and not opened.returned:
                raise UncertainOperation('dlopen entered without a returned receipt')
            if result != OK or not opened.returned or opened.status or not opened.handle:
                raise OpenError('dlopen failed for '+os.fsdecode(path))
            # handle= attaches only a wrapper. It does not dlopen a second time.
            owner._library = C.CDLL(os.fsdecode(path), handle=opened.handle)
            owner._opening = False
            return owner
        except BaseException as error:
            owner._opening = False
            try:
                owner.close()
            except BaseException as cleanup:
                error.add_note('Loading cleanup unresolved; inspect runtime.live_owners: '+repr(cleanup))
            raise

    @property
    def open_receipt(self):
        return _receipt(self._opened)

    @property
    def close_receipt(self):
        return _receipt(self._closed)

    @property
    def closed(self):
        return _closed(self._closed)

    @property
    def resolved(self):
        """Reference consumed, or acquisition durably known not to have occurred."""
        opened = self._opened
        outcome = opened.outcome
        return self.closed or (bool(outcome & 0xffffffff) and bool(outcome >> 32)) or \
            (not opened.entered and not self._opening)

    @property
    def library(self):
        if self.closed:
            return None
        closed = self.close_receipt
        opened = self.open_receipt
        if (closed.entered and not closed.returned) or (opened.entered and not opened.returned):
            raise UncertainOperation('Library reference has an uncertain operation')
        if self._library is None:
            raise LoadingError('Library wrapper setup did not complete; owner still retained')
        return self._library

    def close(self):
        if self.closed:
            self._runtime._retire(self)
            return
        opened = self.open_receipt
        if opened.entered and not opened.returned:
            raise UncertainOperation('Cannot close an uncertain dlopen')
        if not opened.entered or (opened.returned and opened.status != 0):
            if not opened.entered and self._opening:
                raise UncertainOperation('Library open is still preparing its C entry')
            self._runtime._retire(self)
            return  # no reference was acquired
        closed = self.close_receipt
        if closed.entered and not closed.returned:
            raise UncertainOperation('Cannot retry an uncertain dlclose')
        try:
            result = self._runtime._close(C.byref(self._opened), C.byref(self._closed))
            if result == UNCERTAIN:
                raise UncertainOperation('dlclose is already in progress or uncertain')
            if result != OK or not self.closed:
                raise CloseError('dlclose did not record successful reference consumption')
        finally:
            self._runtime._retire(self)

    def __enter__(self):
        return self

    def __exit__(self, *exception):
        self.close()


class LibraryScope:
    """Explicit request acquisitions; baseline owners are never inferred by path.

    Keep this scope on the Database before passing it to Module/build. Failed
    constructors and interrupted open returns need no completed local assignment
    to keep the acquired reference reachable for the guard and later cleanup.
    """
    __slots__ = ('_owners',)

    def __init__(self):
        self._owners = set()

    @property
    def live_owners(self):
        for owner in tuple(self._owners):
            if owner.resolved:
                self._owners.discard(owner)
        return tuple(self._owners)
