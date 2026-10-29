"""Private additive process/lease receipt owners. See LIFECYCLE.md for contracts.

Installation is an explicit offline host operation. No runtime build/import of
the builder occurs here. The fixed NODELETE image is retained until OS teardown.
These receipts track acquisition and release, without physical-resource budgets.
"""
from __future__ import annotations
import ctypes as C
from dataclasses import dataclass
import hashlib
import io
import json
import os
from pathlib import Path
import re
import threading
from .loading import LibraryOwner, Runtime as LoadingRuntime

ABI = 1
OK, ERROR, BAD_ABI, UNCERTAIN, CLOSED, BINDING, RESULT = range(7)
READY, CALLING, RETURNED, CANCELLED = range(4)
TERMINAL, EXIT_OBSERVED = 1, 2


class LifecycleError(RuntimeError): pass
class IdentityMismatch(ValueError): pass
class UncertainOperation(LifecycleError): pass
class ProcessError(LifecycleError): pass
class ReleaseError(LifecycleError): pass
class InvalidResult(LifecycleError): pass


class _Receipt(C.Structure):
    _fields_ = [('abi', C.c_uint32), ('entered', C.c_uint32), ('outcome', C.c_uint64)]
class _Spawn(C.Structure):
    _fields_ = [('receipt', _Receipt), ('pid', C.c_int32), ('reserved', C.c_uint32)]
class _Finish(C.Structure):
    _fields_ = [('receipt', _Receipt), ('wait_status', C.c_int32), ('kill_error', C.c_uint32)]
class _Process(C.Structure):
    _fields_ = [('abi', C.c_uint32), ('size', C.c_uint32), ('prepare', _Receipt),
                ('spawn', _Spawn), ('finish', _Finish), ('fds', C.c_int32*4),
                ('gate', C.c_uint32), ('flags', C.c_uint32),
                ('observed_status', C.c_int32), ('io_error', C.c_uint32)]
class _Call(C.Structure):
    _fields_ = [('abi', C.c_uint32), ('state', C.c_uint32), ('outcome', C.c_uint64),
                ('function', C.c_void_p), ('arity', C.c_uint32), ('reserved', C.c_uint32)]
class ReleaseReceipt(C.Structure):
    _fields_ = [('receipt', _Receipt), ('function', C.c_void_p), ('lease', C.c_uint64)]

    def __init__(self):
        super().__init__(receipt=_Receipt(abi=ABI))

    @property
    def status(self):
        return _snapshot(self.receipt)

    @property
    def consumed(self):
        return _success(self.receipt) and bool(self.function) and bool(self.lease)

class _Descriptor(C.Structure):
    _fields_ = [(key, C.c_uint32) for key in ('abi', 'size', 'process_bytes',
        'receipt_bytes', 'spawn_bytes', 'finish_bytes', 'call_bytes', 'release_bytes',
        'pointer_bytes', 'reserved')] + [('flags', C.c_uint64), ('build_identity', C.c_char*64)]

assert [C.sizeof(t) for t in (_Receipt, _Spawn, _Finish, _Process, _Call, ReleaseReceipt, _Descriptor)] \
    == [16, 24, 24, 104, 32, 32, 112]
assert C.sizeof(C.c_void_p) == 8 and _Receipt.outcome.offset == 8


@dataclass(frozen=True)
class ReceiptStatus:
    abi: int
    entered: bool
    returned: bool
    status: int

def _snapshot(native):
    pair = native.outcome  # one aligned scalar read, matching the C atomic pair
    return ReceiptStatus(native.abi, bool(native.entered), bool(pair & 0xffffffff), pair >> 32)

def _success(native):
    return native.abi == ABI and bool(native.entered) and native.outcome == 1

def _pointer(function):
    if isinstance(function, int):
        if not 0 < function < 2**64:
            raise ValueError('Invalid trusted function address')
        return function
    pointer = C.cast(function, C.c_void_p).value
    if not pointer:
        raise ValueError('Null trusted function address')
    return pointer


_runtime = None
_runtime_lock = threading.RLock()


class LifecycleRuntime:
    __slots__ = ('_identity', '_path', '_state', '_owner', '_processes', '_leases',
                 '_prepare', '_start', '_poll', '_stop', '_close_process', '_invoke', '_cancel', '_release')

    def __init__(self):
        raise TypeError('Install with LifecycleRuntime.load explicitly')

    @classmethod
    def current(cls):
        if _runtime is None or _runtime._state != 'ready':
            raise LifecycleError('Install the fixed lifecycle runtime before requests')
        return _runtime

    @classmethod
    def load(cls, path, *, manifest=None, loading_runtime=None):
        global _runtime
        path = Path(os.path.abspath(os.fsdecode(os.fspath(path))))
        if manifest is None:
            manifest = json.loads(path.with_suffix(path.suffix+'.json').read_text())
        elif isinstance(manifest, (str, os.PathLike)):
            manifest = json.loads(Path(manifest).read_text())
        expected = dict(abiVersion=1, descriptorBytes=112, processBytes=104, receiptBytes=16,
                        spawnBytes=24, finishBytes=24, callBytes=32, releaseBytes=32,
                        pointerBytes=8, flags=15, nodelete=True)
        if any(type(manifest.get(k)) is not type(v) or manifest[k] != v for k, v in expected.items()):
            raise IdentityMismatch('Lifecycle manifest ABI/layout/profile mismatch')
        identity = tuple(manifest.get(key) for key in ('buildIdentitySha256', 'moduleSha256'))
        if any(not isinstance(x, str) or not re.fullmatch('[0-9a-f]{64}', x) for x in identity):
            raise IdentityMismatch('Lifecycle manifest identity is absent')
        if hashlib.sha256(path.read_bytes()).hexdigest() != identity[1]:
            raise IdentityMismatch('Lifecycle file hash mismatch')
        loading_runtime = LoadingRuntime.current() if loading_runtime is None else loading_runtime
        with _runtime_lock:
            if _runtime is not None:
                if _runtime.identity != identity:
                    raise IdentityMismatch('Lifecycle identity is fixed for this process')
                if _runtime._state != 'ready':
                    raise LifecycleError('Lifecycle bootstrap failed/uncertain; restart process')
                return _runtime
            runtime = object.__new__(cls)
            runtime._identity, runtime._path, runtime._state = identity, path, 'loading'
            runtime._owner = None
            runtime._processes, runtime._leases = set(), set()
            _runtime = runtime  # reserve the single bootstrap BEFORE acquisition
            try:
                runtime._owner = LibraryOwner.open(loading_runtime, path)
                runtime._install()
                runtime._state = 'ready'
                return runtime
            except BaseException:
                runtime._state = 'failed'
                # Any unresolved loading owner remains in loading.live_owners.
                # NODELETE retains the fixed image as baseline even on failure.
                raise

    @property
    def identity(self): return self._identity

    def _install(self):
        library = self._owner.library
        describe = library.jaydb_lifecycle_describe_v1
        describe.argtypes, describe.restype = [], C.POINTER(_Descriptor)
        pointer = describe()
        if not pointer:
            raise IdentityMismatch('Loaded lifecycle descriptor is absent')
        d = pointer.contents
        expected = (1, 112, 104, 16, 24, 24, 32, 32, 8, 0, 15)
        fields = ('abi', 'size', 'process_bytes', 'receipt_bytes', 'spawn_bytes', 'finish_bytes',
                  'call_bytes', 'release_bytes', 'pointer_bytes', 'reserved', 'flags')
        if tuple(getattr(d, key) for key in fields) != expected or \
                bytes(d.build_identity) != self.identity[0].encode('ascii'):
            raise IdentityMismatch('Loaded lifecycle descriptor/identity mismatch')
        if hashlib.sha256(self._path.read_bytes()).hexdigest() != self.identity[1]:
            raise IdentityMismatch('Lifecycle file changed during load')
        for attribute, name, arguments in (
            ('_prepare', 'process_prepare_v1', [C.POINTER(_Process)]),
            ('_start', 'process_start_v1', [C.POINTER(_Process), C.POINTER(C.c_char_p), C.POINTER(C.c_char_p)]),
            ('_poll', 'process_poll_v1', [C.POINTER(_Process)]),
            ('_stop', 'process_stop_v1', [C.POINTER(_Process)]),
            ('_close_process', 'process_close_v1', [C.POINTER(_Process)]),
            ('_invoke', 'invoke_v3', [C.c_void_p, C.c_uint32, C.c_void_p, C.c_void_p, C.c_void_p, C.POINTER(_Call)]),
            ('_cancel', 'cancel_v1', [C.POINTER(_Call)]),
            ('_release', 'release_v3', [C.c_void_p, C.c_uint64, C.POINTER(ReleaseReceipt)])):
            function = getattr(library, 'jaydb_lifecycle_'+name)
            function.argtypes, function.restype = arguments, C.c_int
            setattr(self, attribute, function)

    @property
    def live_processes(self):
        for owner in tuple(self._processes):
            if owner.closed: self._processes.discard(owner)
        return tuple(self._processes)

    @property
    def live_leases(self):
        for owner in tuple(self._leases):
            if owner.resolved: self._leases.discard(owner)
        return tuple(self._leases)

    def has_live_leases(self, library_owner):
        return any(owner.library_owner is library_owner for owner in self.live_leases)

    def release_v3(self, function, lease, receipt):
        """Low-level trusted API; caller retains function/DSO/result until resolved."""
        if type(lease) is not int or not 0 < lease < 2**64 or not isinstance(receipt, ReleaseReceipt):
            raise ValueError('Expected a real uint64 lease and a preallocated ReleaseReceipt')
        return self._release(_pointer(function), lease, C.byref(receipt))


class ProcessOwner:
    __slots__ = ('_runtime', '_native', '_argv_bytes', '_env_bytes', '_argv', '_env',
                 '_stdout', '_stderr', '__weakref__')

    def __init__(self): raise TypeError('Use ProcessOwner.prepare')

    @classmethod
    def prepare(cls, runtime, argv, env=None):
        if not isinstance(runtime, LifecycleRuntime) or runtime._state != 'ready':
            raise LifecycleError('Explicit lifecycle installation required')
        if isinstance(argv, (str, bytes)):
            raise ValueError('argv must be a sequence of arguments')
        argv_bytes = tuple(os.fsencode(arg) for arg in argv)
        if not argv_bytes or not argv_bytes[0] or any(b'\0' in arg for arg in argv_bytes):
            raise ValueError('Expected a nonempty argv without embedded NUL')
        environment = dict(os.environ if env is None else env)
        normalized = {}
        for key, value in environment.items():
            key, value = os.fsencode(key), os.fsencode(value)
            if not key or b'=' in key or b'\0' in key or b'\0' in value:
                raise ValueError('Invalid environment entry')
            normalized[key] = value
        normalized[b'BEND_NO_TELEMETRY'] = b'1'
        entries = [key+b'='+value for key, value in normalized.items()]
        owner = object.__new__(cls)
        owner._runtime = runtime
        owner._argv_bytes, owner._env_bytes = argv_bytes, tuple(entries)
        owner._argv = (C.c_char_p*(len(argv_bytes)+1))(*argv_bytes, None)
        owner._env = (C.c_char_p*(len(entries)+1))(*entries, None)
        owner._native = _Process(abi=1, size=C.sizeof(_Process), prepare=_Receipt(abi=1),
            spawn=_Spawn(receipt=_Receipt(abi=1)), finish=_Finish(receipt=_Receipt(abi=1)),
            fds=(C.c_int32*4)(-1, -1, -1, -1))
        owner._stdout = owner._stderr = None
        try:
            runtime._processes.add(owner)  # before pipe2, not merely before spawn
            code = runtime._prepare(C.byref(owner._native))
            if code != OK or not _success(owner._native.prepare):
                owner._error('pipe preparation', code, owner.prepare_receipt)
            owner._stdout = io.FileIO(owner._native.fds[0], 'rb', closefd=False)
            owner._stderr = io.FileIO(owner._native.fds[2], 'rb', closefd=False)
            return owner
        except BaseException as error:
            try: owner.close()
            except BaseException as cleanup:
                error.add_note('Process owner retained in live_processes: '+repr(cleanup))
            raise

    @property
    def prepare_receipt(self): return _snapshot(self._native.prepare)
    @property
    def spawn_receipt(self): return _snapshot(self._native.spawn.receipt)
    @property
    def finish_receipt(self): return _snapshot(self._native.finish.receipt)
    @property
    def closed(self): return bool(self._native.flags & TERMINAL)
    @property
    def pid(self):
        receipt = self.spawn_receipt
        if receipt.entered and not receipt.returned:
            raise UncertainOperation('Spawn entered without a durable returned receipt')
        return self._native.spawn.pid if receipt.returned and receipt.status == 0 else None
    @property
    def stdout(self): return self._stdout if self._native.fds[0] >= 0 else None
    @property
    def stderr(self): return self._stderr if self._native.fds[2] >= 0 else None
    @property
    def returncode(self):
        return os.waitstatus_to_exitcode(self._native.finish.wait_status) if _success(self._native.finish.receipt) else None

    def _error(self, operation, code, receipt=None):
        if code == UNCERTAIN:
            raise UncertainOperation(operation+' is in progress or uncertain')
        raise ProcessError(f'{operation} failed: code={code}, receipt={receipt}, io_errno={self._native.io_error}')

    def start(self):
        if self._stdout is None or self._stderr is None:
            raise ProcessError('Streams must be prearmed before start')
        code = self._runtime._start(C.byref(self._native), self._argv, self._env)
        if code != OK or not _success(self._native.spawn.receipt):
            self._error('spawn', code, self.spawn_receipt)
        return self

    def poll(self):
        """Observe exit with WNOWAIT; never reap or release the group identity."""
        code = self._runtime._poll(C.byref(self._native))
        if code != OK: self._error('waitid WNOWAIT', code)
        return bool(self._native.flags & EXIT_OBSERVED) or _success(self._native.finish.receipt)

    def stop_and_wait(self):
        code = self._runtime._stop(C.byref(self._native))
        if code != OK: self._error('killpg-before-wait', code, self.finish_receipt)
        return self.returncode

    wait = stop_and_wait

    def close(self):
        try:
            code = self._runtime._close_process(C.byref(self._native))
            if code != OK: self._error('process close', code, self.finish_receipt)
        finally:
            if self.closed:
                self._runtime._processes.discard(self)
                # Wrappers never own the descriptors, so retrying their close
                # cannot accidentally close a newly reused FD number.
                try:
                    if self._stdout is not None: self._stdout.close()
                finally:
                    if self._stderr is not None: self._stderr.close()


class OutputLease:
    __slots__ = ('_runtime', '_library_owner', '_native', '_result_owner', '_function',
                 '_function_address', '_call', '_release_receipt', '_run_function', '_arguments', '__weakref__')

    def __init__(self): raise TypeError('Use OutputLease.prepare before native run')

    @classmethod
    def prepare(cls, runtime, library_owner, native_result, *, result_owner=None):
        if not isinstance(runtime, LifecycleRuntime) or runtime._state != 'ready':
            raise LifecycleError('Explicit lifecycle installation required')
        if not isinstance(library_owner, LibraryOwner) or library_owner.library is None:
            raise LifecycleError('A live LibraryOwner is required')
        # Validate the byte-output prefix shared by the supported native ABIs.
        offsets = dict(status=0, output=16, output_len=24, output_capacity=32, lease=40)
        if not isinstance(native_result, C.Structure) or C.sizeof(native_result) != 136 or \
                any(getattr(type(native_result), k, None) is None or
                    getattr(type(native_result), k).offset != v for k, v in offsets.items()):
            raise ValueError('Expected the unchanged 136-byte native ResultV3')
        if native_result.lease or native_result.output or native_result.output_len or native_result.output_capacity:
            raise ValueError('Prepare a fresh result before run, never adopt an already acquired output')
        function = library_owner.library.jaydb_native_release_v3
        function.argtypes, function.restype = [C.c_uint64], C.c_uint32
        owner = object.__new__(cls)
        owner._runtime, owner._library_owner = runtime, library_owner
        owner._native = native_result
        owner._result_owner = native_result if result_owner is None else result_owner
        owner._function, owner._function_address = function, _pointer(function)
        owner._call, owner._release_receipt = _Call(abi=1), ReleaseReceipt()
        owner._run_function = None
        owner._arguments = ()
        runtime._leases.add(owner)  # before ANY native run acquires its output
        return owner

    @property
    def library_owner(self): return self._library_owner
    @property
    def native_result(self): return self._native
    @property
    def release_receipt(self): return self._release_receipt.status
    @property
    def call_state(self): return self._call.state
    @property
    def call_status(self):
        pair = self._call.outcome
        return pair >> 32 if pair & 0xffffffff else None
    @property
    def resolved(self):
        native, receipt = self._native, self._release_receipt
        if receipt.consumed:
            return (receipt.function == self._function_address and receipt.lease == native.lease
                    and native.status == 0 and self._call.state == RETURNED)
        empty = not (native.lease or native.output or native.output_len or native.output_capacity)
        return empty and (self._call.state == CANCELLED or
            (self._call.state == RETURNED and self.call_status == native.status and native.status != 0))

    def invoke(self, function, *pointer_args):
        if self._library_owner.library is None:
            raise LifecycleError('Target library already closed')
        if len(pointer_args) not in (2, 3):
            raise ValueError('Native V3 run ABI takes two or three pointers')
        address = _pointer(function)
        arguments = tuple(C.cast(arg, C.c_void_p) for arg in pointer_args)
        if C.addressof(self._native) not in tuple(arg.value for arg in arguments[1:]):
            raise ValueError('Native call must write the prearmed ResultV3 address')
        self._run_function = function
        self._arguments = pointer_args
        code = self._runtime._invoke(address, len(arguments), *arguments,
            *([None] if len(arguments) == 2 else []), C.byref(self._call))
        if code == UNCERTAIN: raise UncertainOperation('Native call is in progress or uncertain')
        if code != OK or self._call.state != RETURNED:
            raise LifecycleError('Native invoke refused: '+str(code))
        return self.call_status

    def release(self):
        try:
            if self.resolved: return
            if self._call.state == READY:
                code = self._runtime._cancel(C.byref(self._call))
                if code == UNCERTAIN: raise UncertainOperation('Native call is in progress')
                if code != OK: raise LifecycleError('Native call cancellation refused: '+str(code))
            if self.resolved: return
            if self._call.state == CALLING:
                raise UncertainOperation('Native run entered without a returned C receipt')
            native = self._native
            if self._call.state != RETURNED or self.call_status != native.status or \
                    native.status != 0 or not native.lease or native.output_len > native.output_capacity or \
                    (native.output_len and not native.output):
                raise InvalidResult('Native result/lease does not match its returned call receipt')
            if self._library_owner.library is None:
                raise LifecycleError('Pending lease lost its live DSO owner; refuse function call')
            code = self._runtime.release_v3(self._function_address, native.lease, self._release_receipt)
            if code == UNCERTAIN: raise UncertainOperation('Lease release entered without returned receipt')
            if code != OK or not self.resolved:
                raise ReleaseError('Lease not consumed: '+str(self.release_receipt))
        finally:
            if self.resolved: self._runtime._leases.discard(self)

    close = release
