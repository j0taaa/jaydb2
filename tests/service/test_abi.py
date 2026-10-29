"""Exact byte/deadline conversions with explicit Python call fixtures.

These fixtures do not model durable C receipts or acquired DSO references.
Real interruption/receipt/lease ownership is checked in test_native_abi,
test_lifecycle and test_lifecycle_consumers.
"""
import ctypes as C
from pathlib import Path
import sys
import time
from types import SimpleNamespace
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from tools.service.abi import Module, NativeFailure, Ns128, addressable_ceiling


class OwnedLibrary:
    def __init__(self, *, status=0, corrupt=False, preparation=False, release_status=0):
        self.status, self.corrupt = status, corrupt
        self.preparation, self.release_status = preparation, release_status
        self.released = []
        self.output = (C.c_uint8 * 3)(0, 128, 255)

    def jaydb_native_run_v3(self, request, result):
        self.request = request._obj
        r = result._obj
        r.status = self.status
        if not self.status:
            r.output = self.output
            r.output_len = 4 if self.corrupt else 3
            r.output_capacity = 3
            r.lease = 7
        if self.preparation:
            r.stage = 2
            r.preparation_started_ns = Ns128.duration(time.monotonic_ns() - 10**9)
        return self.status

    def jaydb_native_release_v3(self, lease):
        self.released.append(lease)
        return self.release_status


class AbsoluteLibrary(OwnedLibrary):
    def jaydb_native_run_deadline_v3(self, request, result, deadline):
        self.absolute_deadline = deadline._obj.natural()
        return self.jaydb_native_run_v3(request, result)


class ConversionFixtureModule(Module):
    class Call:
        def invoke(self,function,*args):
            return function(*args)

    def _prepare_output(self,native_result,*,result_owner=None):
        self._fixture_result=native_result
        return self.Call()

    def _release_outputs(self):
        r=getattr(self,'_fixture_result',None)
        self._fixture_result=None
        if r is not None and r.status==0 and r.lease:
            if self.library.jaydb_native_release_v3(r.lease):
                raise RuntimeError('Native output lease release failed (Python conversion fixture)')


def module(library):
    m = ConversionFixtureModule.__new__(ConversionFixtureModule)
    m._library_owner = SimpleNamespace(library=library) # explicit ABI fixture; no acquired dlopen reference
    m.preparation_deadline = None
    return m


class AbiOwnership(unittest.TestCase):
    def run_module(self, lib, **extra):
        return module(lib).run(b'in', capacity=10**5000, memory=10**5000,
            timeout_ns=10**5000, **extra)

    def test_huge_limits_copy_only_actual_owned_bytes_then_release(self):
        lib = OwnedLibrary()
        self.assertEqual(self.run_module(lib), b'\0\x80\xff')
        self.assertEqual(lib.released, [7])
        self.assertEqual(lib.request.input_len, 2)
        self.assertEqual(lib.request.memory_bytes, 2**64 - 1)
        self.assertEqual(lib.request.output_limit, 2**64 - 1)
        self.assertEqual(lib.request.setup_timeout_ns.natural(), 2**128 - 1)

    def test_failed_copy_releases_lease(self):
        lib = OwnedLibrary()
        with patch('tools.service.abi.C.string_at', side_effect=MemoryError('copy')):
            with self.assertRaises(MemoryError):
                self.run_module(lib)
        self.assertEqual(lib.released, [7])

    def test_exception_at_ctypes_return_releases_written_lease(self):
        class RaisedAtReturn(OwnedLibrary):
            def jaydb_native_run_v3(self, request, result):
                super().jaydb_native_run_v3(request, result)
                raise RuntimeError('return dispatch')
        lib = RaisedAtReturn()
        with self.assertRaisesRegex(RuntimeError, 'return dispatch'):
            self.run_module(lib)
        self.assertEqual(lib.released, [7])

    def test_invalid_result_releases_lease(self):
        lib = OwnedLibrary(corrupt=True)
        with self.assertRaisesRegex(RuntimeError, 'Invalid native result'):
            self.run_module(lib)
        self.assertEqual(lib.released, [7])

    def test_native_failure_has_no_release(self):
        lib = OwnedLibrary(status=3)
        with self.assertRaises(NativeFailure) as failure:
            self.run_module(lib)
        self.assertEqual(failure.exception.status, 3)
        self.assertEqual(lib.released, [])

    def test_preparation_deadline_still_applies_after_copy_and_release(self):
        lib = OwnedLibrary(preparation=True)
        with self.assertRaises(NativeFailure) as failure:
            self.run_module(lib, execution_ns=10**500, preparation_ns=1)
        self.assertEqual(failure.exception.stage, 2)
        self.assertEqual(lib.released, [7])

    def test_release_failure_prevents_return_to_publication(self):
        with self.assertRaisesRegex(RuntimeError, 'lease release failed'):
            self.run_module(OwnedLibrary(release_status=5))

    def test_durations_preserve_values_above_u64_and_timespec_domain(self):
        for n in (1, 2**64, (2**63 - 1) * 10**9 + 999999999, 2**128 - 1):
            self.assertEqual(Ns128.duration(n).natural(), n)
        self.assertEqual(Ns128.duration(10**5000).natural(), 2**128 - 1)
        self.assertEqual(addressable_ceiling(10**5000), 2**64 - 1)
        for invalid in (0, -1, 1.5, True):
            with self.assertRaises(ValueError):
                Ns128.duration(invalid)

    def test_parent_deadline_crosses_the_ffi_without_renewal(self):
        lib = AbsoluteLibrary()
        m = module(lib)
        m.absolute_setup = m.automatic_terms = True
        m.minimum_native_stack = 20480
        # The caller sampled a 1000-ns remaining duration at t=9000. Its actual
        # deadline stays 10000 after Python/ctypes preparation, now at t=9600.
        with patch('tools.service.abi.time.monotonic_ns', return_value=9600):
            self.assertEqual(m.run(b'in', capacity=3, memory=4 * 1024**2,
                timeout_ns=1000, setup_deadline_ns=10000), b'\0\x80\xff')
        self.assertEqual(lib.absolute_deadline, 10000)
        self.assertEqual(lib.request.setup_timeout_ns.natural(), 400)
        self.assertEqual(lib.request.term_stack_bytes, 0)
        self.assertEqual(lib.released, [7])

    def test_expired_absolute_deadline_never_starts_native_execution(self):
        for deadline in (0, 10000):
            lib = AbsoluteLibrary()
            m = module(lib)
            m.absolute_setup = True
            with patch('tools.service.abi.time.monotonic_ns', return_value=10000):
                with self.assertRaises(NativeFailure) as failure:
                    m.run(b'in', capacity=3, memory=4 * 1024**2,
                        timeout_ns=1000, setup_deadline_ns=deadline)
            self.assertEqual((failure.exception.status, failure.exception.stage), (3, 0))
            self.assertFalse(hasattr(lib, 'request'))
            self.assertEqual(lib.released, [])

    def test_automatic_native_stack_has_no_budget_dependent_partition(self):
        lib = AbsoluteLibrary()
        m = module(lib)
        m.absolute_setup = m.automatic_terms = m.automatic_native = True
        for memory in (1,4*1024**2,10**5000):
            self.assertEqual(m.run(b'in',capacity=3,memory=memory,timeout_ns=10**9,
                setup_deadline_ns=time.monotonic_ns()+10**9),b'\0\x80\xff')
            self.assertEqual(lib.request.term_stack_bytes,0)
            self.assertEqual(lib.request.native_stack_bytes,0)

    def test_missing_absolute_interface_cannot_silently_renew_a_deadline(self):
        lib = OwnedLibrary()
        with self.assertRaisesRegex(RuntimeError, 'absolute setup deadline interface required'):
            module(lib).run(b'in', capacity=3, memory=4 * 1024**2,
                timeout_ns=1000, setup_deadline_ns=time.monotonic_ns() + 1000)
        self.assertFalse(hasattr(lib, 'request'))

    def test_exception_at_absolute_entry_return_releases_written_lease(self):
        class RaisedAtReturn(AbsoluteLibrary):
            def jaydb_native_run_deadline_v3(self, request, result, deadline):
                super().jaydb_native_run_deadline_v3(request, result, deadline)
                raise RuntimeError('absolute return dispatch')
        lib = RaisedAtReturn()
        m = module(lib)
        m.absolute_setup = True
        with self.assertRaisesRegex(RuntimeError, 'absolute return dispatch'):
            m.run(b'in', capacity=3, memory=4 * 1024**2, timeout_ns=10**9,
                setup_deadline_ns=time.monotonic_ns() + 10**9)
        self.assertEqual(lib.released, [7])


if __name__ == '__main__':
    unittest.main()
