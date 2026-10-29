"""Bytes-only ctypes binding to the checked native CPU1 module ABI."""
from __future__ import annotations
import ctypes as C
import hashlib
import json
import os
from pathlib import Path
import time
from .loading import LibraryOwner,Runtime
from .lifecycle import LifecycleRuntime, OutputLease

U64 = C.c_uint64
U32 = C.c_uint32
PTR = C.POINTER(C.c_uint8)


class Request(C.Structure):
    _fields_ = [('abi_version', U32), ('flags', U32), ('input', PTR), ('input_len', U64),
        ('output', PTR), ('output_capacity', U64), ('memory_bytes', U64), ('timeout_ns', U64),
        ('term_stack_bytes', U64), ('native_stack_bytes', U64)]


class Result(C.Structure):
    _fields_ = [('status', U32), ('runtime_code', U32), ('output_len', U64),
                ('elapsed_ns', U64), ('charged_bytes', U64)]


class RequestV2(C.Structure):
    _fields_ = [('base', Request), ('execution_timeout_ns', U64), ('preparation_timeout_ns', U64)]


class ResultV2(C.Structure):
    _fields_ = [('base', Result), ('stage', U32), ('reserved', U32),
                ('setup_ns', U64), ('execution_ns', U64), ('preparation_ns', U64)]


class Ns128(C.Structure):
    _fields_ = [('lo', U64), ('hi', U64)]

    @classmethod
    def duration(cls, n):
        if type(n) is not int or n <= 0:
            raise ValueError('Native duration must be a positive Nat')
        # Every valid target timespec is below 2**93 ns. This representation
        # therefore preserves every observable expiration comparison, even
        # when the public duration is a Nat larger than the native word pair.
        n = min(n, 2**128 - 1)
        return cls(n & (2**64 - 1), n >> 64)

    def natural(self):
        return self.lo + (self.hi << 64)


class RequestV3(C.Structure):
    _fields_ = [('abi_version', U32), ('flags', U32), ('input', PTR), ('input_len', U64),
        ('output_limit', U64), ('memory_bytes', U64), ('term_stack_bytes', U64),
        ('native_stack_bytes', U64), ('setup_timeout_ns', Ns128),
        ('execution_timeout_ns', Ns128), ('preparation_timeout_ns', Ns128)]


class ResultV3(C.Structure):
    _fields_ = [('status', U32), ('runtime_code', U32), ('stage', U32), ('reserved', U32),
        ('output', PTR), ('output_len', U64), ('output_capacity', U64), ('lease', U64),
        ('charged_bytes', U64), ('elapsed_ns', Ns128), ('stage_elapsed_ns', Ns128 * 3),
        ('preparation_started_ns', Ns128)]


class Descriptor(C.Structure):
    _fields_ = [('abi_version', U32), ('flags', U32), ('generic_nat_array', U32),
        ('immortal_refcounts', U32), ('image_bytes', U64), ('maximum_c_frame_bytes', U64),
        ('generated_c_sha256', C.c_char_p)]


class NativeFailure(RuntimeError):
    def __init__(self, status, runtime_code, stage=0):
        self.status, self.runtime_code, self.stage = status, runtime_code, stage
        super().__init__(f'Runtime status={status}, code={runtime_code}, stage={stage}')


class NativeOwnershipPending(Exception):
    """Cleanup is unresolved; this cannot justify completing a public error."""


def exact_u64(n):
    if not isinstance(n, int) or not 0 <= n < 2**64:
        raise ValueError('ABI integer outside uint64')
    return n


def addressable_ceiling(n):
    if type(n) is not int or n < 0:
        raise ValueError('Native byte ceiling must be a Nat')
    # No byte extent addressable on this target can exceed UINT64_MAX.
    # This clips only a logical bound; it allocates no corresponding buffer.
    return min(n, 2**64 - 1)


class Module:
    def __init__(self, file: Path, *, loading_runtime=None, lifecycle_runtime=None, library_scope=None):
        self._library_owner = None
        self._lifecycle_runtime = LifecycleRuntime.current() if lifecycle_runtime is None else lifecycle_runtime
        self.preparation_deadline = None
        report = json.loads(file.with_suffix(file.suffix + '.json').read_text())
        if hashlib.sha256(file.read_bytes()).hexdigest() != report['moduleSha256']:
            raise RuntimeError('Native module hash mismatch')
        runtime=Runtime.current() if loading_runtime is None else loading_runtime
        try:
            self._library_owner=LibraryOwner.open(runtime,file,scope=library_scope)
            lib=self.library
            if not report.get('ownedOutputV3') or not report.get('demandStableHeapV3') or report.get('durationBitsV3') != 128:
                raise RuntimeError('Native V3 allocation/time interface required')
            for version in (1, 2, 3):
                describe = getattr(lib, f'jaydb_native_describe_v{version}')
                describe.argtypes, describe.restype = [], C.POINTER(Descriptor)
                d = describe().contents
                if (d.abi_version != version or d.flags != 1 or d.generic_nat_array != 1
                    or d.immortal_refcounts != 1 or d.generated_c_sha256.decode() != report['sourceSha256']
                    or d.image_bytes != report['imageBytes']):
                    raise RuntimeError('Native descriptor mismatch')
            lib.jaydb_native_run_v1.argtypes = [C.POINTER(Request), C.POINTER(Result)]
            lib.jaydb_native_run_v1.restype = U32
            lib.jaydb_native_run_v2.argtypes = [C.POINTER(RequestV2), C.POINTER(ResultV2)]
            lib.jaydb_native_run_v2.restype = U32
            lib.jaydb_native_preparation_started_v2.argtypes = []
            lib.jaydb_native_preparation_started_v2.restype = U64
            lib.jaydb_native_run_v3.argtypes = [C.POINTER(RequestV3), C.POINTER(ResultV3)]
            lib.jaydb_native_run_v3.restype = U32
            self.absolute_setup = bool(report.get('absoluteSetupDeadlineV3'))
            if self.absolute_setup:
                lib.jaydb_native_run_deadline_v3.argtypes = [C.POINTER(RequestV3), C.POINTER(ResultV3), C.POINTER(Ns128)]
                lib.jaydb_native_run_deadline_v3.restype = U32
            self.automatic_terms = bool(report.get('automaticTermStackV3'))
            self.automatic_native = bool(report.get('automaticNativeStackV3'))
            if self.automatic_native and (report.get('automaticNativeStackModeV3') != 'linux-main-growdown'
                or not report.get('nativeStackClashProtection')):
                raise RuntimeError('Unrecognized automatic native stack contract')
            self.minimum_native_stack = report.get('minimumExplicitNativeStackBytes', 512 * 1024)
            if type(self.minimum_native_stack) is not int or self.minimum_native_stack <= 0:
                raise RuntimeError('Invalid native stack metadata')
            lib.jaydb_native_release_v3.argtypes = [U64]
            lib.jaydb_native_release_v3.restype = U32
        except BaseException:
            self.close()
            raise

    def close(self):
        if self._library_owner is not None:
            # The runtime retains pending results and the DSO owner even if
            # this Module loses its last Python reference after an exception.
            try:
                self._release_outputs()
            finally:
                runtime = getattr(self, '_lifecycle_runtime', None)
                if runtime is None or not runtime.has_live_leases(self._library_owner):
                    self._library_owner.close()

    def _release_outputs(self):
        runtime = getattr(self, '_lifecycle_runtime', None)
        if runtime is None:
            return  # close-only fixtures never execute a native call
        try:
            for owner in runtime.live_leases:
                if owner.library_owner is self._library_owner:
                    owner.release()
            if runtime.has_live_leases(self._library_owner):
                raise NativeOwnershipPending('Native output ownership remains unresolved')
        except NativeOwnershipPending:
            raise
        except BaseException as error:
            # Include registry enumeration itself in the guard. Failure before
            # owner.release() must not escape as a completed public failure.
            if runtime.has_live_leases(self._library_owner):
                raise NativeOwnershipPending('Native output lease remains retained') from error
            raise

    def _prepare_output(self, native_result, *, result_owner=None):
        self._release_outputs()
        return OutputLease.prepare(self._lifecycle_runtime, self._library_owner,
                                   native_result, result_owner=result_owner)

    @property
    def library(self):
        owner=self._library_owner
        return None if owner is None else owner.library

    def run(self, data: bytes, *, capacity: int, memory: int, timeout_ns: int,
            execution_ns=None, preparation_ns=None, setup_deadline_ns=None):
        if self.library is None:
            raise RuntimeError('Module closed')
        self.preparation_deadline = None
        absolute_setup = getattr(self, 'absolute_setup', False)
        if setup_deadline_ns is not None:
            if type(setup_deadline_ns) is not int or setup_deadline_ns < 0:
                raise ValueError('Setup deadline must be an exact CLOCK_MONOTONIC epoch')
            if not absolute_setup:
                raise RuntimeError('Native absolute setup deadline interface required')
            setup_deadline = setup_deadline_ns
        else:
            setup_deadline = time.monotonic_ns() + timeout_ns
        if time.monotonic_ns() >= setup_deadline:
            raise NativeFailure(3, 0, 0)
        inp = (C.c_uint8 * max(1, len(data))).from_buffer_copy(data or b'\0')
        limit = addressable_ceiling(capacity)
        # Current modules use the main Linux grow-down stack, whose process
        # limit the Database host removes before initialization. There is no
        # budget-dependent C-stack subdivision in that mode. Keep the explicit
        # historical mode for archived V3 modules used by compatibility tests.
        page = os.sysconf('SC_PAGE_SIZE')
        auto_terms = getattr(self, 'automatic_terms', False)
        auto_native = getattr(self, 'automatic_native', False)
        stack = 0
        if not auto_terms or not auto_native:
            stack = min(8 * 1024**2, max(256 * 1024, memory // 16))
            stack = ((stack + page - 1) // page) * page
        # New builders report the actual page-aligned native minimum. Historical
        # modules use the earlier 512-KiB floor. A nonaligned public Nat budget
        # must never manufacture ARGUMENT at this boundary.
        native_stack = 0 if auto_native else (
            ((max(stack, getattr(self, 'minimum_native_stack', 512 * 1024)) + page - 1) // page) * page)
        setup_left = setup_deadline - time.monotonic_ns()
        if setup_left <= 0:
            raise NativeFailure(3, 0, 0)
        request = RequestV3(3, 1, inp, exact_u64(len(data)), limit, addressable_ceiling(memory),
            0 if auto_terms else stack, native_stack, Ns128.duration(setup_left),
            Ns128.duration(timeout_ns if execution_ns is None else execution_ns),
            Ns128.duration(timeout_ns if preparation_ns is None else preparation_ns))
        result = ResultV3()
        absolute = Ns128.duration(setup_deadline) if absolute_setup else None
        # Register the result BEFORE C can acquire output. The invocation and
        # release receipts remain reachable through the runtime on every exit.
        try:
            owner = self._prepare_output(result)
            if absolute_setup:
                status = owner.invoke(self.library.jaydb_native_run_deadline_v3,
                                      C.byref(request), C.byref(result), C.byref(absolute))
            else:
                status = owner.invoke(self.library.jaydb_native_run_v3,
                                      C.byref(request), C.byref(result))
            lease = result.lease if result.status == 0 else 0
            if (status != result.status or result.stage > 2 or result.reserved
                or result.output_len > limit or result.output_len > result.output_capacity
                or (result.output_len and not result.output)):
                raise RuntimeError('Invalid native result')
            if status:
                if result.lease or result.output_len or result.output_capacity or result.output:
                    raise RuntimeError('Failed native call retained output')
                raise NativeFailure(status, result.runtime_code, result.stage)
            if not lease:
                raise RuntimeError('Native success without output lease')
            started = result.preparation_started_ns.natural()
            if started:
                self.preparation_deadline = started + preparation_ns if preparation_ns is not None else started + timeout_ns
            data = C.string_at(result.output, result.output_len) if result.output_len else b''
        finally:
            self._release_outputs()
        if execution_ns is not None:
            if self.preparation_deadline is None:
                raise RuntimeError('Execution ended without preparation stage')
            if time.monotonic_ns() >= self.preparation_deadline:
                raise NativeFailure(3, 0, 2)
        return data
