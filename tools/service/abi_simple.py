"""Bytes-only native ABI6 binding, using durable loading and output receipts.

The admitted Book and source/proof gate remain the host's responsibility.
Build hashes identify the loaded artifacts; they do not prove equivalence.
"""
from __future__ import annotations
import ctypes as C
import hashlib
import json
from pathlib import Path
import re

from .loading import LibraryOwner, Runtime
from .lifecycle import LifecycleRuntime, OutputLease

U32, U64 = C.c_uint32, C.c_uint64
PTR = C.POINTER(C.c_uint8)


class Request(C.Structure):
    _fields_ = [('abi_version', U32), ('size', U32), ('input', PTR),
                ('input_len', U64), ('output_capacity', U64)]


class Result(C.Structure):
    _fields_ = [('status', U32), ('runtime_code', U32), ('stage', U32), ('reserved', U32),
                ('output', PTR), ('output_len', U64), ('output_capacity', U64),
                ('lease', U64), ('compatibility_reserved', C.c_uint8 * 88)]


class Descriptor(C.Structure):
    _fields_ = [(key, U32) for key in ('abi_version', 'size', 'request_bytes',
        'result_bytes', 'result_prefix_bytes', 'flags', 'term_bytes', 'reserved')] + [
        ('source_sha256', C.c_char * 64), ('build_identity_sha256', C.c_char * 64)]


assert (C.sizeof(Request), C.sizeof(Result), C.sizeof(Descriptor)) == (32, 136, 160)
assert (Result.output.offset, Result.lease.offset) == (16, 40)


class NativeFailure(RuntimeError):
    def __init__(self, status, runtime_code, stage=0):
        self.status, self.runtime_code, self.stage = status, runtime_code, stage
        self.fatal = status != 7  # only the logical output byte ceiling is recoverable
        self.infrastructure = status in (1, 2, 5)
        super().__init__(f'Native ABI6 status={status}, code={runtime_code}, stage={stage}')


class NativeInfrastructureFailure(NativeFailure):
    """A real allocation, platform, or native invocation failure."""


class NativeOwnershipPending(Exception):
    """Keep the instance and its DSO alive until durable ownership resolves."""


class SimpleModule:
    def __init__(self, file, loading_runtime=None, lifecycle_runtime=None, library_scope=None):
        self._library_owner = None
        self._lifecycle_runtime = LifecycleRuntime.current() if lifecycle_runtime is None else lifecycle_runtime
        runtime = Runtime.current() if loading_runtime is None else loading_runtime
        file = Path(file).resolve()
        report = json.loads(file.with_suffix(file.suffix+'.json').read_text())
        expected = dict(simpleABI6=True, abiVersion=6, requestBytes=32, resultBytes=136,
            resultPrefixBytes=48, descriptorBytes=160, termBytes=24, flags=1,
            ownedOutput=True, nativeExecution='same-process-main-thread',
            nativeStack='linux-main-growdown', nativeStackClashProtection=True)
        if any(type(report.get(key)) is not type(value) or report[key] != value
               for key, value in expected.items()):
            raise RuntimeError('Native ABI6 manifest/profile mismatch')
        for key in ('moduleSha256', 'sourceSha256', 'preparedSourceSha256', 'buildIdentitySha256'):
            if not isinstance(report.get(key), str) or not re.fullmatch('[0-9a-f]{64}', report[key]):
                raise RuntimeError('Native ABI6 manifest identity missing: '+key)
        if hashlib.sha256(file.read_bytes()).hexdigest() != report['moduleSha256']:
            raise RuntimeError('Native ABI6 file hash mismatch')
        self.report = report
        try:
            self._library_owner = LibraryOwner.open(runtime, file, scope=library_scope)
            library = self.library
            describe = library.jaydb_native_describe_v6
            describe.argtypes, describe.restype = [], C.POINTER(Descriptor)
            pointer = describe()
            if not pointer:
                raise RuntimeError('Native ABI6 descriptor absent')
            descriptor = pointer.contents
            fields = ('abi_version', 'size', 'request_bytes', 'result_bytes',
                      'result_prefix_bytes', 'flags', 'term_bytes', 'reserved')
            if tuple(getattr(descriptor, key) for key in fields) != (6, 160, 32, 136, 48, 1, 24, 0) or \
                    bytes(descriptor.source_sha256) != report['sourceSha256'].encode('ascii') or \
                    bytes(descriptor.build_identity_sha256) != report['buildIdentitySha256'].encode('ascii'):
                raise RuntimeError('Loaded native ABI6 descriptor/identity mismatch')
            if hashlib.sha256(file.read_bytes()).hexdigest() != report['moduleSha256']:
                raise RuntimeError('Native ABI6 file changed during load')
            self._run = library.jaydb_native_run_v6
            self._run.argtypes, self._run.restype = [C.POINTER(Request), C.POINTER(Result)], U32
        except BaseException as error:
            try:
                self.close()
            except BaseException as cleanup:
                error.add_note('Native library owner retained after setup failure: '+repr(cleanup))
            raise

    @property
    def library(self):
        return None if self._library_owner is None else self._library_owner.library

    def _release_outputs(self):
        owner, runtime = self._library_owner, self._lifecycle_runtime
        if owner is None:
            return
        try:
            for lease in runtime.live_leases:
                if lease.library_owner is owner:
                    lease.release()
            if runtime.has_live_leases(owner):
                raise NativeOwnershipPending('Native output ownership remains unresolved')
        except BaseException as error:
            if runtime.has_live_leases(owner):
                raise NativeOwnershipPending('Native output lease and DSO remain retained') from error
            raise

    def close(self):
        if self._library_owner is None:
            return
        try:
            self._release_outputs()
        finally:
            if not self._lifecycle_runtime.has_live_leases(self._library_owner):
                self._library_owner.close()

    def run(self, data: bytes, *, capacity: int) -> bytes:
        if not isinstance(data, bytes):
            raise TypeError('Native input must be bytes')
        if type(capacity) is not int or capacity < 0:
            raise ValueError('Output capacity must be a natural byte count')
        if self.library is None:
            raise RuntimeError('Native module closed')
        self._release_outputs()
        # Logical output ceiling only: every addressable extent fits uint64.
        ceiling = min(capacity, 2**64-1)
        source = (C.c_uint8 * max(1, len(data))).from_buffer_copy(data or b'\0')
        request = Request(6, C.sizeof(Request), source, len(data), ceiling)
        result = Result()
        lease = OutputLease.prepare(self._lifecycle_runtime, self._library_owner, result,
                                    result_owner=(source, request, result))
        try:
            status = lease.invoke(self._run, C.byref(request), C.byref(result))
            if status != result.status or result.reserved or any(result.compatibility_reserved):
                raise RuntimeError('Native ABI6 result/receipt mismatch')
            if status:
                if result.output or result.output_len or result.output_capacity or result.lease:
                    raise RuntimeError('Failed native ABI6 result retained output')
                failure = NativeInfrastructureFailure if status in (1, 2, 5) else NativeFailure
                raise failure(status, result.runtime_code, result.stage)
            if not result.lease or result.output_len > ceiling or result.output_len > result.output_capacity or \
                    (result.output_len and not result.output):
                raise RuntimeError('Invalid native ABI6 output extent/lease')
            return C.string_at(result.output, result.output_len) if result.output_len else b''
        finally:
            self._release_outputs()

    def __enter__(self):
        return self

    def __exit__(self, *exception):
        self.close()
