"""Bytes-only binding to the synchronous native ABI6."""
from __future__ import annotations
import ctypes as C
import hashlib
import json
from pathlib import Path
import re

from .loading import LibraryOwner, OwnershipError

U32, U64 = C.c_uint32, C.c_uint64
PTR = C.POINTER(C.c_uint8)


class Request(C.Structure):
    _fields_ = [('abi_version', U32), ('size', U32), ('input', PTR),
                ('input_len', U64), ('output_capacity', U64)]


class Result(C.Structure):
    _fields_ = [('status', U32), ('runtime_code', U32), ('stage', U32), ('reserved', U32),
                ('output', PTR), ('output_len', U64), ('output_capacity', U64), ('lease', U64)]


class Descriptor(C.Structure):
    _fields_ = [(key, U32) for key in ('abi_version', 'size', 'request_bytes',
        'result_bytes', 'flags', 'term_bytes')] + [
        ('source_sha256', C.c_char * 64), ('build_identity_sha256', C.c_char * 64)]


assert (C.sizeof(Request), C.sizeof(Result), C.sizeof(Descriptor)) == (32, 48, 152)
assert (Result.output.offset, Result.lease.offset) == (16, 40)


class NativeFailure(RuntimeError):
    def __init__(self, status, runtime_code, stage=0):
        self.status, self.runtime_code, self.stage = status, runtime_code, stage
        self.fatal = status != 7  # only the logical output byte ceiling is recoverable
        super().__init__(f'Native ABI6 status={status}, code={runtime_code}, stage={stage}')


class SimpleModule:
    def __init__(self, file):
        self._retained = None
        self._failed = False
        file = Path(file).resolve()
        report = json.loads(file.with_suffix(file.suffix+'.json').read_text())
        expected = dict(simpleABI6=True, abiVersion=6, requestBytes=32, resultBytes=48,
            descriptorBytes=152, termBytes=24, flags=1, ownedOutput=True,
            nativeExecution='same-process-main-thread',
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
        self._owner = LibraryOwner(file)
        try:
            with self._owner.using() as library:
                describe = library.jaydb_native_describe_v6
                describe.argtypes, describe.restype = [], C.POINTER(Descriptor)
                pointer = describe()
                if not pointer:
                    raise RuntimeError('Native ABI6 descriptor absent')
                descriptor = pointer.contents
                fields = ('abi_version', 'size', 'request_bytes', 'result_bytes', 'flags', 'term_bytes')
                if tuple(getattr(descriptor, key) for key in fields) != (6, 152, 32, 48, 1, 24) or \
                        bytes(descriptor.source_sha256) != report['sourceSha256'].encode('ascii') or \
                        bytes(descriptor.build_identity_sha256) != report['buildIdentitySha256'].encode('ascii'):
                    raise RuntimeError('Loaded native ABI6 descriptor/identity mismatch')
                if hashlib.sha256(file.read_bytes()).hexdigest() != report['moduleSha256']:
                    raise RuntimeError('Native ABI6 file changed during load')
                self._run = library.jaydb_native_run_v6
                self._run.argtypes, self._run.restype = [C.POINTER(Request), C.POINTER(Result)], U32
                self._release = library.jaydb_native_release_v6
                self._release.argtypes, self._release.restype = [U64], U32
        except BaseException:
            self.close()
            raise

    def close(self):
        if self._retained is not None:
            raise OwnershipError('Native call or output still owns this library')
        self._owner.close()
        self._run = self._release = None

    def _uncertain(self, message):
        self._owner.poison()
        return OwnershipError(message)

    def run(self, data: bytes, *, capacity: int) -> bytes:
        if not isinstance(data, bytes):
            raise TypeError('Native input must be bytes')
        if type(capacity) is not int or capacity < 0:
            raise ValueError('Output capacity must be a natural byte count')
        if self._failed:
            raise RuntimeError('Native module failed; restart the instance')
        with self._owner.using():
            ceiling = min(capacity, 2**64-1)
            source = (C.c_uint8 * max(1, len(data))).from_buffer_copy(data or b'\0')
            request = Request(6, C.sizeof(Request), source, len(data), ceiling)
            result = Result()
            self._retained = source, request, result
            try:
                status = self._run(C.byref(request), C.byref(result))
            except BaseException as error:
                raise self._uncertain('Native return is uncertain; stop the instance') from error
            if status != result.status or result.reserved or result.stage > 2:
                raise self._uncertain('Invalid native ABI6 result')
            if status:
                if result.output or result.output_len or result.output_capacity or result.lease:
                    raise self._uncertain('Failed native ABI6 result retained output')
                self._retained = None
                self._failed = status != 7
                raise NativeFailure(status, result.runtime_code, result.stage)
            if not result.lease or result.output_len > ceiling or result.output_len > result.output_capacity or \
                    (result.output_len and not result.output):
                raise self._uncertain('Invalid native ABI6 output extent/lease')
            try:
                return C.string_at(result.output, result.output_len) if result.output_len else b''
            finally:
                try:
                    released = self._release(result.lease)
                except BaseException as error:
                    raise self._uncertain('Native release is uncertain; never retry') from error
                if released:
                    raise self._uncertain('Native output release failed; stop the instance')
                self._retained = None

    def __enter__(self):
        return self

    def __exit__(self, *exception):
        self.close()
