"""Local causal tests; injected errors/native semantics are explicit fixtures.
No existing consumer is patched or integrated by this suite. Synchronous C
syscalls, real signals, malloc/free, destructor effects and subprocess identity
checks are distinguished from injected Python failures.
"""
from __future__ import annotations
import ctypes as C
import gc
import hashlib
import inspect
import json
import os
from pathlib import Path
import resource
import selectors
import signal
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from unittest import mock
import weakref

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.service import build_lifecycle as builder, build_loading, lifecycle as L, loading


class Ns(C.Structure): _fields_ = [('lo', C.c_uint64), ('hi', C.c_uint64)]
class NativeResult(C.Structure):
    _fields_ = [(k, C.c_uint32) for k in ('status', 'runtime_code', 'stage', 'reserved')] + [
        ('output', C.c_void_p)] + [(k, C.c_uint64) for k in
        ('output_len', 'output_capacity', 'lease', 'charged_bytes')] + [
        ('elapsed', Ns), ('stages', Ns*3), ('preparation', Ns)]
class AccountedResult(C.Structure):
    _fields_ = [('native', NativeResult), ('remaining', C.c_uint8*520)]
class Stats(C.Structure):
    _fields_ = [(key, C.c_uint64) for key in
        ('runs', 'allocations', 'releases', 'release_calls', 'destructors', 'live_at_destructor')]
assert C.sizeof(NativeResult) == 136 and C.sizeof(AccountedResult) == 656


class LifecycleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory(prefix='jaydb2-lifecycle-test-')
        cls.output = Path(cls.directory.name)
        cls.loading_path, cls.path = cls.output/'loading.so', cls.output/'lifecycle.so'
        cls.loading_report = build_loading.build(cls.loading_path)
        cls.loading = loading.Runtime.load(cls.loading_path, manifest=cls.loading_report)
        cls.report = builder.build(cls.path)
        cls.runtime = L.LifecycleRuntime.load(cls.path, manifest=cls.report, loading_runtime=cls.loading)
        cls.helper = cls.output/'helper'
        cls.native = cls.output/'native.so'
        subprocess.run([str(builder.COMPILER), '-O2', '-Wall', '-Wextra', '-Werror',
                        str(ROOT/'tests/service/lifecycle_process_fixture.c'), '-o', str(cls.helper)], check=True)
        subprocess.run([str(builder.COMPILER), '-O2', '-Wall', '-Wextra', '-Werror', '-shared', '-fPIC',
                        str(ROOT/'tests/service/lifecycle_native_fixture.c'), '-o', str(cls.native)], check=True)
        # Explicit TEST DSO; not installed as LifecycleRuntime and never given
        # a production manifest. Selected C entry points alone are patched in
        # directed tests, so report flags cannot activate these wrappers.
        wrapped = cls.output/'wrapped-syscalls.so'
        subprocess.run([str(builder.COMPILER), '-O2', '-std=c11', '-Wall', '-Wextra', '-Werror',
                        '-shared', '-fPIC', '-Wl,-z,nodelete',
                        '-Wl,--wrap=posix_spawnp,--wrap=pipe2,--wrap=waitpid,--wrap=close,--wrap=waitid,--wrap=kill',
                        '-DJAYDB_LIFECYCLE_BUILD_ID="'+('f'*64)+'"',
                        str(ROOT/'tools/service/lifecycle.c'),
                        str(ROOT/'tests/service/lifecycle_syscall_fixture.c'), '-o', str(wrapped)], check=True)
        cls.wrapped = C.CDLL(str(wrapped), mode=os.RTLD_NOW | os.RTLD_NODELETE)
        cls.wrapped.lifecycle_syscall_fixture_mode.argtypes = [C.c_int]
        cls.wrapped.lifecycle_syscall_fixture_mode.restype = None
        cls.wrapped.lifecycle_syscall_fixture_kills.argtypes = []
        cls.wrapped.lifecycle_syscall_fixture_kills.restype = C.c_uint
        for suffix, original in (('prepare', cls.runtime._prepare), ('start', cls.runtime._start),
                                 ('stop', cls.runtime._stop), ('close', cls.runtime._close_process)):
            function = getattr(cls.wrapped, 'jaydb_lifecycle_process_'+suffix+'_v1')
            function.argtypes, function.restype = original.argtypes, original.restype
        cls.core = resource.getrlimit(resource.RLIMIT_CORE)
        resource.setrlimit(resource.RLIMIT_CORE, (0, cls.core[1]))

    @classmethod
    def tearDownClass(cls):
        try:
            assert cls.runtime.live_processes == (), cls.runtime.live_processes
            assert cls.runtime.live_leases == (), cls.runtime.live_leases
        finally:
            resource.setrlimit(resource.RLIMIT_CORE, cls.core)
            cls.directory.cleanup()

    def setUp(self):
        self.stats = Stats()
        self.log_path = os.fsencode(self.output/(self._testMethodName+'.log'))

    def process(self, *args):
        owner = L.ProcessOwner.prepare(self.runtime, [self.helper, *args],
            env={**os.environ, 'LIFECYCLE_TEST_EXTRA': 'present'})
        self.addCleanup(owner.close)
        return owner

    def drain(self, owner):
        parts = {owner.stdout: [], owner.stderr: []}
        deadline = time.monotonic()+5
        with selectors.DefaultSelector() as ready:
            for stream in parts: ready.register(stream, selectors.EVENT_READ)
            while ready.get_map():
                if time.monotonic() >= deadline: raise TimeoutError('fixture drain')
                for event, _ in ready.select(.05):
                    chunk = os.read(event.fd, 65536)
                    if chunk: parts[event.fileobj].append(chunk)
                    else: ready.unregister(event.fileobj)
        # Group identity is still pinned; poll never reaped the leader.
        self.assertTrue(owner.poll())
        owner.stop_and_wait()
        return tuple(b''.join(chunks) for chunks in parts.values())

    def lease(self, *, release_error=0, run_error=0, release_signal=0, run_signal=0,
              release_delay=0, accounted=False):
        library_owner = loading.LibraryOwner.open(self.loading, self.native)
        self.addCleanup(library_owner.close)
        configure = library_owner.library.lifecycle_fixture_configure
        configure.argtypes = [C.POINTER(Stats), C.c_char_p, C.c_uint32, C.c_uint32,
                              C.c_int, C.c_int, C.c_uint]
        configure.restype = None
        configure(C.byref(self.stats), self.log_path, release_error, run_error,
                  release_signal, run_signal, release_delay)
        result_owner = AccountedResult() if accounted else NativeResult()
        native = result_owner.native if accounted else result_owner
        pending = L.OutputLease.prepare(self.runtime, library_owner, native, result_owner=result_owner)
        self.addCleanup(pending.release)
        function = library_owner.library.lifecycle_fixture_accounted if accounted else library_owner.library.lifecycle_fixture_run
        arguments = (None, None, C.byref(native)) if accounted else (None, C.byref(native))
        return pending, library_owner, result_owner, function, arguments

    def invoke(self, pending, function, arguments):
        self.assertEqual(pending.invoke(function, *arguments), pending.native_result.status)

    def guarded_close(self, library_owner):
        # The separate consumer integration MUST implement this guard. This
        # local harness models it without editing Module/controller/accounted.
        if self.runtime.has_live_leases(library_owner):
            raise L.LifecycleError('pending output; do not dlclose')
        library_owner.close()

    def alarm(self):
        def raised(*_): raise KeyboardInterrupt('real SIGALRM')
        old = signal.signal(signal.SIGALRM, raised)
        self.addCleanup(signal.signal, signal.SIGALRM, old)

    def probe(self, body):
        header = ('import sys,ctypes as C,os,json,resource,signal\nfrom pathlib import Path\n'
                  'resource.setrlimit(resource.RLIMIT_CORE,(0,resource.getrlimit(resource.RLIMIT_CORE)[1]))\n'
                  'sys.path.insert(0,'+repr(str(ROOT))+')\n'
                  'from tools.service import lifecycle as L,loading,build_lifecycle as builder\n'
                  'from unittest import mock\n'
                  'loading.Runtime.load('+repr(str(self.loading_path))+')\n'
                  'path=Path('+repr(str(self.path))+')\n')
        return subprocess.run([sys.executable, '-B', '-c', header+body], cwd=ROOT, text=True,
                              check=True, capture_output=True, timeout=30)

    def test_process_profile_stdin_env_close_fds_setsid_core_and_pipes(self):
        with tempfile.TemporaryFile() as inherited:
            os.set_inheritable(inherited.fileno(), True)
            before = os.fstat(0)
            owner = self.process('profile', str(inherited.fileno()))
            self.assertIsNone(owner.pid)
            self.assertIn(owner, self.runtime.live_processes)
            self.assertFalse(owner.stdout.closefd)
            self.assertFalse(os.get_blocking(owner.stdout.fileno()))
            owner.start()
            out, err = self.drain(owner)
        fields = dict(item.split('=', 1) for item in out.decode().split())
        self.assertEqual(fields['pid'], str(owner.pid))
        self.assertEqual(fields['pid'], fields['pgid'])
        self.assertEqual(fields['pid'], fields['sid'])
        self.assertEqual(fields['core'], '0')
        self.assertEqual(int(fields['hard']), resource.getrlimit(resource.RLIMIT_CORE)[1] % 2**64)
        self.assertEqual(fields['fd_closed'], '1')
        self.assertEqual((int(fields['stdin_dev']), int(fields['stdin_ino'])), (before.st_dev, before.st_ino))
        self.assertEqual((fields['telemetry'], fields['extra']), ('1', 'present'))
        self.assertEqual(err, b'stderr captured\n')
        self.assertEqual(owner.returncode, 0)
        pid = owner.pid
        with self.assertRaises(ChildProcessError): os.waitpid(pid, os.WNOHANG)
        owner.close()
        self.assertTrue(owner.closed)
        self.assertIsNone(owner.stdout)

    def test_many_stdout_stderr_without_size_cap(self):
        owner = self.process('many').start()
        out, err = self.drain(owner)
        self.assertEqual(out, b'o'*(8192*80))
        self.assertEqual(err, b'e'*(8192*80))

    def test_telemetry_cannot_be_overridden_by_mixed_bytes_and_string_env_keys(self):
        owner = L.ProcessOwner.prepare(self.runtime, [self.helper, 'profile'], env={
            b'BEND_NO_TELEMETRY': b'0', 'BEND_NO_TELEMETRY': '0',
            b'LIFECYCLE_TEST_EXTRA': b'present'})
        self.addCleanup(owner.close)
        owner.start()
        out, _ = self.drain(owner)
        self.assertIn(b'telemetry=1', out)

    def test_exit_wnowait_keeps_identity_and_kill_before_reap(self):
        owner = self.process('exit', '19').start()
        deadline = time.monotonic()+5
        while not owner.poll() and time.monotonic() < deadline: time.sleep(.001)
        observed = os.waitid(os.P_PID, owner.pid, os.WEXITED | os.WNOHANG | os.WNOWAIT)
        self.assertEqual(observed.si_pid, owner.pid)
        self.assertEqual(observed.si_status, 19)
        self.assertEqual(owner.stop_and_wait(), 19)
        real = self.runtime._stop
        # Idempotence is in C as well as in Python; no second kill/reap.
        self.assertEqual(real(C.byref(owner._native)), L.OK)

    def test_stop_and_wait_kills_group_and_reaps_running_leader(self):
        owner = self.process('sleep').start()
        self.assertFalse(owner.poll())
        pid = owner.pid
        self.assertEqual(owner.stop_and_wait(), -signal.SIGKILL)
        self.assertFalse(Path('/proc', str(pid)).exists())
        self.assertEqual(owner.stop_and_wait(), -signal.SIGKILL)

    def test_stop_after_leader_exit_kills_same_group_descendant(self):
        owner = self.process('descendant').start()
        data = b''
        deadline = time.monotonic()+5
        while b'\n' not in data and time.monotonic() < deadline:
            try: data += os.read(owner.stdout.fileno(), 100)
            except BlockingIOError: time.sleep(.001)
        descendant = int(data)
        while not owner.poll() and time.monotonic() < deadline: time.sleep(.001)
        self.assertEqual(os.getpgid(descendant), owner.pid)
        owner.stop_and_wait()
        # An orphan can remain a zombie until init reaps it; it must not run.
        while Path('/proc', str(descendant), 'stat').exists() and time.monotonic() < deadline:
            if Path('/proc', str(descendant), 'stat').read_text().split()[2] == 'Z': break
            time.sleep(.001)
        if Path('/proc', str(descendant), 'stat').exists():
            self.assertEqual(Path('/proc', str(descendant), 'stat').read_text().split()[2], 'Z')

    def test_real_exec_error_has_no_waitable_child_and_no_retry_spawn(self):
        owner = L.ProcessOwner.prepare(self.runtime, [self.output/'missing-helper'])
        self.addCleanup(owner.close)
        with self.assertRaises(L.ProcessError): owner.start()
        self.assertEqual(owner.spawn_receipt.status, 2)  # ENOENT, not a memory witness
        self.assertIsNone(owner.pid)
        with self.assertRaises(L.ProcessError): owner.start()
        owner.close()
        self.assertTrue(owner.closed)

    def test_process_preentry_error_retains_prearmed_owner_and_allows_retry(self):
        owner = self.process('sleep')
        with mock.patch.object(self.runtime, '_start', side_effect=MemoryError('before spawn C')):
            with self.assertRaises(MemoryError): owner.start()
        self.assertFalse(owner.spawn_receipt.entered)
        self.assertIn(owner, self.runtime.live_processes)
        owner.start()
        owner.close()
        self.assertTrue(owner.closed)

    def test_spawn_post_c_exception_has_pid_before_python_return(self):
        owner = self.process('sleep')
        real = self.runtime._start
        def interrupted(*args):
            self.assertEqual(real(*args), L.OK)
            raise MemoryError('after real spawn')
        with mock.patch.object(self.runtime, '_start', interrupted):
            with self.assertRaises(MemoryError): owner.start()
        pid = owner.pid
        self.assertGreater(pid, 0)
        self.assertIn(owner, self.runtime.live_processes)
        owner.close()
        self.assertFalse(Path('/proc', str(pid)).exists())

    def test_real_signal_after_spawn_before_ffi_assignment_has_durable_pid(self):
        owner = self.process('sleep')
        self.alarm()
        real = self.runtime._start
        def interrupted(*args):
            result = real(*args)
            signal.raise_signal(signal.SIGALRM)  # real signal, controlled post-C placement
            return result
        with mock.patch.object(self.runtime, '_start', interrupted):
            with self.assertRaises(KeyboardInterrupt): owner.start()
        self.assertTrue(owner.spawn_receipt.returned)
        pid = owner.pid
        owner.close()
        self.assertFalse(Path('/proc', str(pid)).exists())

    def test_real_sigalrm_inside_posix_spawnp_preserves_pid_at_ffi_return(self):
        self.alarm()
        owner = self.process('sleep')
        self.wrapped.lifecycle_syscall_fixture_mode(1)
        with mock.patch.object(self.runtime, '_start', self.wrapped.jaydb_lifecycle_process_start_v1):
            with self.assertRaises(KeyboardInterrupt): owner.start()
        self.assertEqual(owner.spawn_receipt, L.ReceiptStatus(1, True, True, 0))
        pid = owner.pid
        self.assertEqual(os.getpgid(pid), pid)
        owner.close()
        self.assertFalse(Path('/proc', str(pid)).exists())

    def test_real_sigalrm_inside_pipe2_keeps_preparation_acquisitions_owned(self):
        self.alarm()
        before = set(os.listdir('/proc/self/fd'))
        self.wrapped.lifecycle_syscall_fixture_mode(2)
        with mock.patch.object(self.runtime, '_prepare', self.wrapped.jaydb_lifecycle_process_prepare_v1):
            with self.assertRaises(KeyboardInterrupt): self.process('sleep')
        self.assertEqual(self.runtime.live_processes, ())
        self.assertEqual(set(os.listdir('/proc/self/fd')), before)

    def test_real_sigalrm_inside_waitpid_preserves_reap_and_prevents_second_kill(self):
        self.alarm()
        owner = self.process('sleep').start()
        self.wrapped.lifecycle_syscall_fixture_mode(3)
        with mock.patch.object(self.runtime, '_stop', self.wrapped.jaydb_lifecycle_process_stop_v1):
            with self.assertRaises(KeyboardInterrupt): owner.stop_and_wait()
            self.assertEqual(owner.finish_receipt, L.ReceiptStatus(1, True, True, 0))
            self.assertEqual(owner.stop_and_wait(), -signal.SIGKILL)
        self.assertEqual(self.wrapped.lifecycle_syscall_fixture_kills(), 1)

    def test_real_sigalrm_inside_fd_close_has_durable_terminal_state(self):
        self.alarm()
        owner = self.process('sleep').start()
        self.wrapped.lifecycle_syscall_fixture_mode(4)
        with mock.patch.object(self.runtime, '_close_process', self.wrapped.jaydb_lifecycle_process_close_v1):
            with self.assertRaises(KeyboardInterrupt): owner.close()
            self.assertTrue(owner.closed)
            owner.close()
        self.assertTrue(all(fd == -1 for fd in owner._native.fds))
        self.assertEqual(self.wrapped.lifecycle_syscall_fixture_kills(), 1)

    def test_second_pipe_error_fixture_closes_first_pipe_and_is_not_memory_witness(self):
        before = set(os.listdir('/proc/self/fd'))
        self.wrapped.lifecycle_syscall_fixture_mode(5)
        with mock.patch.object(self.runtime, '_prepare', self.wrapped.jaydb_lifecycle_process_prepare_v1):
            with self.assertRaises(L.ProcessError) as error: self.process('sleep')
        self.assertIn('status=12', str(error.exception))
        self.assertEqual(self.runtime.live_processes, ())
        self.assertEqual(set(os.listdir('/proc/self/fd')), before)

    def test_echild_fixture_refuses_to_kill_unverified_group_and_retains_owner(self):
        owner = self.process('sleep').start()
        self.wrapped.lifecycle_syscall_fixture_mode(6)
        with mock.patch.object(self.runtime, '_stop', self.wrapped.jaydb_lifecycle_process_stop_v1):
            with self.assertRaises(L.ProcessError): owner.stop_and_wait()
            self.assertEqual(self.wrapped.lifecycle_syscall_fixture_kills(), 0)
        self.assertIn(owner, self.runtime.live_processes)
        self.assertIsNone(owner.returncode)
        self.assertEqual(os.getpgid(owner.pid), owner.pid)
        # This is a synthetic ECHILD, not an actual foreign reaper. The real
        # child is still waitable and the valid retry can kill/reap it.
        owner.stop_and_wait()

    def test_lost_process_owner_is_retained_without_last_local_reference(self):
        owner = self.process('sleep').start()
        self._cleanups.pop()
        reference, pid = weakref.ref(owner), owner.pid
        del owner
        gc.collect()
        retained, = self.runtime.live_processes
        self.assertIs(reference(), retained)
        retained.close()
        del retained
        gc.collect()
        self.assertIsNone(reference())
        self.assertFalse(Path('/proc', str(pid)).exists())

    def test_pipe_post_c_exception_and_wrapper_failure_close_known_fds(self):
        before = set(os.listdir('/proc/self/fd'))
        real = self.runtime._prepare
        def interrupted(*args):
            self.assertEqual(real(*args), L.OK)
            raise MemoryError('after real pipe2')
        with mock.patch.object(self.runtime, '_prepare', interrupted):
            with self.assertRaises(MemoryError): self.process('sleep')
        self.assertEqual(self.runtime.live_processes, ())
        self.assertEqual(set(os.listdir('/proc/self/fd')), before)
        with mock.patch.object(L.io, 'FileIO', side_effect=MemoryError('wrapper')):
            with self.assertRaises(MemoryError): self.process('sleep')
        self.assertEqual(self.runtime.live_processes, ())
        self.assertEqual(set(os.listdir('/proc/self/fd')), before)

    def test_pipe_failure_and_cleanup_failure_keeps_registered_owner(self):
        real = self.runtime._prepare
        def interrupted(*args): real(*args); raise MemoryError('post-pipes')
        with mock.patch.object(self.runtime, '_prepare', interrupted), \
                mock.patch.object(self.runtime, '_close_process', side_effect=MemoryError('cleanup preentry')):
            with self.assertRaises(MemoryError): self.process('sleep')
        retained, = self.runtime.live_processes
        self.assertIsNone(retained.pid)
        self.assertTrue(retained.prepare_receipt.returned)
        self.assertTrue(all(fd >= 0 for fd in retained._native.fds))
        retained.close()

    def test_process_close_post_c_exception_cannot_repeat_kill_or_fd_close(self):
        owner = self.process('sleep').start()
        real = self.runtime._close_process
        calls = []
        def interrupted(*args): calls.append(real(*args)); raise MemoryError('after teardown C')
        with mock.patch.object(self.runtime, '_close_process', interrupted):
            with self.assertRaises(MemoryError): owner.close()
        self.assertTrue(owner.closed)
        self.assertEqual(calls, [L.OK])
        self.assertTrue(all(fd == -1 for fd in owner._native.fds))
        owner.close()

    def test_armed_process_is_not_retired_during_inspection_before_c_prepare(self):
        real = self.runtime._prepare
        def inspect_before(*args):
            owner, = self.runtime.live_processes
            self.assertFalse(owner.prepare_receipt.entered)
            self.assertEqual(self.runtime.live_processes, (owner,))
            return real(*args)
        with mock.patch.object(self.runtime, '_prepare', inspect_before): owner = self.process('sleep')
        owner.close()

    def test_core_profile_refuses_before_child_without_changing_hard(self):
        if resource.getrlimit(resource.RLIMIT_CORE)[1] == 0: self.skipTest('hard core already zero')
        core = resource.getrlimit(resource.RLIMIT_CORE)
        owner = self.process('sleep')
        try:
            resource.setrlimit(resource.RLIMIT_CORE, (1, core[1]))
            with self.assertRaises(L.ProcessError): owner.start()
            self.assertIsNone(owner.pid)
            self.assertEqual(resource.getrlimit(resource.RLIMIT_CORE), (1, core[1]))
        finally: resource.setrlimit(resource.RLIMIT_CORE, core)

    def test_no_autoreap_profile_is_checked_before_spawn(self):
        owner = self.process('sleep')
        old = signal.signal(signal.SIGCHLD, signal.SIG_IGN)
        try:
            with self.assertRaises(L.ProcessError): owner.start()
            self.assertIsNone(owner.pid)
        finally: signal.signal(signal.SIGCHLD, old)

    def test_output_prearmed_before_run_then_release_before_real_destructor(self):
        pending, library, result, fn, args = self.lease()
        self.assertIn(pending, self.runtime.live_leases)
        self.assertFalse(pending.resolved)
        self.assertTrue(self.runtime.has_live_leases(library))
        self.invoke(pending, fn, args)
        self.assertEqual(C.string_at(result.output, result.output_len), b'leased!')
        pending.release()
        self.assertTrue(pending.resolved)
        self.assertEqual(self.stats.releases, 1)
        self.guarded_close(library)
        self.assertEqual((self.stats.destructors, self.stats.live_at_destructor), (1, 0))
        self.assertEqual(Path(os.fsdecode(self.log_path)).read_text(), 'released\n')
        with mock.patch.object(self.runtime, '_release', side_effect=AssertionError('released function called')):
            pending.release()  # never jumps to the now-unloaded DSO

    def test_accounted_result_656_and_three_pointer_signature_stay_unchanged(self):
        pending, library, result, fn, args = self.lease(accounted=True)
        self.invoke(pending, fn, args)
        self.assertGreater(result.native.lease, 0)
        self.assertIs(pending._result_owner, result)
        pending.release()
        self.guarded_close(library)
        self.assertEqual(self.stats.live_at_destructor, 0)

    def test_empty_success_still_has_and_consumes_its_real_lease(self):
        pending, library, result, fn, args = self.lease(run_error=2**32-1)
        self.invoke(pending, fn, args)
        self.assertEqual((result.status, result.output, result.output_len, result.output_capacity), (0, None, 0, 0))
        self.assertGreater(result.lease, 0)
        self.assertTrue(self.runtime.has_live_leases(library))
        pending.release()
        self.assertEqual(self.stats.release_calls, 1)
        self.guarded_close(library)
        self.assertEqual(self.stats.live_at_destructor, 0)

    def test_pending_lease_refuses_to_call_a_function_when_its_owner_reports_closed(self):
        pending, library, result, fn, args = self.lease()
        self.invoke(pending, fn, args)
        # Negative owner-state fixture; the real DSO stays loaded throughout.
        # Even a consumer violating the required guard cannot cause this API
        # to jump into code whose owner is already known to be closed.
        with mock.patch.object(loading.LibraryOwner, 'library', new_callable=mock.PropertyMock, return_value=None):
            with self.assertRaisesRegex(L.LifecycleError, 'refuse function call'): pending.release()
        self.assertEqual(self.stats.release_calls, 0)
        self.assertIn(pending, self.runtime.live_leases)
        pending.release()
        self.guarded_close(library)
        self.assertEqual(self.stats.live_at_destructor, 0)

    def test_invoke_preentry_error_can_cancel_without_output_and_inspection_never_cancels(self):
        pending, library, result, fn, args = self.lease()
        self.assertEqual(self.runtime.live_leases, (pending,))
        self.assertEqual(pending.call_state, L.READY)
        with mock.patch.object(self.runtime, '_invoke', side_effect=MemoryError('run preentry')):
            with self.assertRaises(MemoryError): pending.invoke(fn, *args)
        self.assertIn(pending, self.runtime.live_leases)
        self.assertFalse(pending.resolved)
        pending.release()
        self.assertEqual(pending.call_state, L.CANCELLED)
        self.assertEqual((self.stats.runs, self.stats.release_calls), (0, 0))
        self.guarded_close(library)
        with self.assertRaises(L.LifecycleError): pending.invoke(fn, *args)

    def test_invoke_rejects_output_pointer_different_from_prearmed_result(self):
        pending, library, result, fn, args = self.lease()
        different = NativeResult()
        with self.assertRaisesRegex(ValueError, 'prearmed ResultV3'):
            pending.invoke(fn, None, C.byref(different))
        self.assertEqual(self.stats.runs, 0)
        pending.release()
        self.guarded_close(library)

    def test_invoke_post_c_exception_preserves_result_and_call_receipt(self):
        pending, library, result, fn, args = self.lease()
        real = self.runtime._invoke
        def interrupted(*args): real(*args); raise MemoryError('native return')
        with mock.patch.object(self.runtime, '_invoke', interrupted):
            with self.assertRaises(MemoryError): pending.invoke(fn, *args)
        self.assertEqual(pending.call_state, L.RETURNED)
        self.assertGreater(result.lease, 0)
        self.assertIn(pending, self.runtime.live_leases)
        pending.release()
        self.guarded_close(library)
        self.assertEqual(self.stats.live_at_destructor, 0)

    def test_real_signal_native_run_return_preserves_lease_before_python_assignment(self):
        self.alarm()
        pending, library, result, fn, args = self.lease(run_signal=signal.SIGALRM)
        with self.assertRaises(KeyboardInterrupt): pending.invoke(fn, *args)
        self.assertEqual(pending.call_state, L.RETURNED)
        self.assertGreater(result.lease, 0)
        pending.release()
        self.guarded_close(library)
        self.assertEqual((self.stats.releases, self.stats.live_at_destructor), (1, 0))

    def test_release_preentry_memory_error_is_strongly_retained_and_blocks_dlclose(self):
        pending, library, result, fn, args = self.lease()
        self.invoke(pending, fn, args)
        with mock.patch.object(self.runtime, '_release', side_effect=MemoryError('release preentry')):
            with self.assertRaises(MemoryError): pending.release()
        self.assertFalse(pending.release_receipt.entered)
        self.assertIn(pending, self.runtime.live_leases)
        with self.assertRaises(L.LifecycleError): self.guarded_close(library)
        self.assertEqual(self.stats.destructors, 0)
        self.assertEqual(C.string_at(result.output, result.output_len), b'leased!')
        pending.release()
        self.guarded_close(library)
        self.assertEqual((self.stats.destructors, self.stats.live_at_destructor), (1, 0))

    def test_real_signal_before_release_c_keeps_lease_and_dso_held(self):
        self.alarm()
        pending, library, _, fn, args = self.lease()
        self.invoke(pending, fn, args)
        lines, first = inspect.getsourcelines(L.OutputLease.release)
        line = first+next(i for i, text in enumerate(lines) if 'code = self._runtime.release_v3' in text)
        armed = True
        def trace(frame, event, arg):
            nonlocal armed
            if armed and event == 'line' and frame.f_code is L.OutputLease.release.__code__ and frame.f_lineno == line:
                armed = False
                signal.raise_signal(signal.SIGALRM)
            return trace
        try:
            sys.settrace(trace)
            with self.assertRaises(KeyboardInterrupt): pending.release()
        finally: sys.settrace(None)
        self.assertFalse(armed)
        self.assertEqual((self.stats.releases, self.stats.destructors), (0, 0))
        with self.assertRaises(L.LifecycleError): self.guarded_close(library)
        pending.release()
        self.guarded_close(library)

    def test_real_signal_after_release_c_never_repeats_consumed_lease(self):
        self.alarm()
        pending, library, _, fn, args = self.lease(release_signal=signal.SIGALRM)
        self.invoke(pending, fn, args)
        with self.assertRaises(KeyboardInterrupt): pending.release()
        self.assertTrue(pending.resolved)
        self.assertEqual(pending.release_receipt, L.ReceiptStatus(1, True, True, 0))
        self.guarded_close(library)
        self.assertEqual((self.stats.release_calls, self.stats.destructors, self.stats.live_at_destructor), (1, 1, 0))
        pending.release()
        self.assertEqual(self.stats.release_calls, 1)

    def test_release_post_c_python_error_and_retirement_error_still_consumed(self):
        pending, library, _, fn, args = self.lease()
        self.invoke(pending, fn, args)
        real = self.runtime._release
        def interrupted(*args): real(*args); raise MemoryError('after release C')
        with mock.patch.object(self.runtime, '_release', interrupted):
            with self.assertRaises(MemoryError): pending.release()
        self.assertTrue(pending.resolved)
        pending.release()
        self.guarded_close(library)
        self.assertEqual(self.stats.release_calls, 1)

    def test_error_without_consumption_fixture_allows_retry_same_function_and_lease(self):
        pending, library, result, fn, args = self.lease(release_error=5)
        self.invoke(pending, fn, args)
        with self.assertRaises(L.ReleaseError): pending.release()
        self.assertEqual(pending.release_receipt, L.ReceiptStatus(1, True, True, 5))
        self.assertFalse(pending.resolved)
        self.assertIn(pending, self.runtime.live_leases)
        self.assertEqual(C.string_at(result.output, result.output_len), b'leased!')
        self.assertEqual(self.runtime.release_v3(pending._function_address, result.lease+1,
                                                pending._release_receipt), L.BINDING)
        self.assertEqual(self.stats.release_calls, 1)
        pending.release()
        self.guarded_close(library)
        self.assertEqual((self.stats.release_calls, self.stats.releases), (2, 1))

    def test_native_failure_has_no_lease_and_never_calls_release_function(self):
        pending, library, result, fn, args = self.lease(run_error=5)
        self.invoke(pending, fn, args)
        self.assertEqual((result.status, result.lease), (5, 0))
        pending.release()
        self.guarded_close(library)
        self.assertEqual((self.stats.allocations, self.stats.release_calls, self.stats.live_at_destructor), (0, 0, 0))

    def test_registry_keeps_result_receipt_function_and_dso_after_local_refs_lost(self):
        pending, library, result, fn, args = self.lease()
        self.invoke(pending, fn, args)
        ref, result_ref, library_ref = weakref.ref(pending), weakref.ref(result), weakref.ref(library)
        self._cleanups.pop()  # release cleanup
        self._cleanups.pop()  # library cleanup
        del pending, library, result, fn, args
        gc.collect()
        retained, = self.runtime.live_leases
        self.assertIs(ref(), retained)
        self.assertIs(result_ref(), retained.native_result)
        self.assertIs(library_ref(), retained.library_owner)
        retained.release()
        self.guarded_close(retained.library_owner)
        self.assertEqual(self.stats.live_at_destructor, 0)
        del retained
        gc.collect()
        self.assertIsNone(ref())

    def test_release_in_progress_uncertain_refuses_retry_without_calling_twice(self):
        pending, library, result, fn, args = self.lease(release_delay=150000)
        self.invoke(pending, fn, args)
        errors = []
        def release():
            try: pending.release()
            except BaseException as error: errors.append(error)
        thread = threading.Thread(target=release)
        thread.start()
        try:
            deadline = time.monotonic()+5
            while not pending.release_receipt.entered and time.monotonic() < deadline: time.sleep(.001)
            with self.assertRaises(L.UncertainOperation): pending.release()
            self.assertFalse(pending.release_receipt.returned)
        finally: thread.join(5)
        self.assertFalse(thread.is_alive())
        self.assertEqual(errors, [])
        self.assertEqual(self.stats.release_calls, 1)
        self.guarded_close(library)

    def test_runtime_singleton_no_hidden_build_and_production_nodelete(self):
        with mock.patch.object(subprocess, 'run', side_effect=AssertionError('hidden build')), \
                mock.patch.object(loading.LibraryOwner, 'open', side_effect=AssertionError('extra load')):
            self.assertIs(L.LifecycleRuntime.load(self.path, manifest=self.report), self.runtime)
            self.assertIs(L.LifecycleRuntime.current(), self.runtime)
        self.assertIn('NODELETE', subprocess.check_output(['readelf', '-d', str(self.path)], text=True))
        self.assertEqual(hashlib.sha256(self.path.read_bytes()).hexdigest(), self.report['moduleSha256'])
        symbols = subprocess.check_output(['nm', '-D', '--defined-only', str(self.path)], text=True)
        self.assertNotIn('fixture', symbols)
        self.assertEqual(len(symbols.splitlines()), 9)

    def test_manifest_hash_layout_and_flags_are_checked_before_loading(self):
        for key, value in [('moduleSha256', '0'*64), ('releaseBytes', 16), ('flags', 0), ('nodelete', False)]:
            with self.subTest(key=key), self.assertRaises(L.IdentityMismatch):
                L.LifecycleRuntime.load(self.path, manifest={**self.report, key: value})

    def test_json_alone_cannot_grant_compiled_lifecycle_identity(self):
        self.probe("""
report=json.loads(path.with_suffix('.so.json').read_text())
report['buildIdentitySha256']='0'*64
try: L.LifecycleRuntime.load(path,manifest=report)
except L.IdentityMismatch as e: assert 'Loaded lifecycle' in str(e)
else: raise AssertionError('JSON granted compiled identity')
""")

    def test_atomic_rebuild_old_dlopen_mapping_cannot_receive_new_identity(self):
        self.probe("""
import tempfile,shutil
with tempfile.TemporaryDirectory() as directory:
    directory=Path(directory);source=directory/'sources';source.mkdir()
    for name in ('lifecycle.h','lifecycle.c','build_lifecycle.py'):
        shutil.copyfile(builder.SOURCE/name,source/name)
    builder.SOURCE=source
    output=directory/'runtime.so'
    first=builder.build(output)
    old=C.CDLL(str(output),mode=os.RTLD_NOW|os.RTLD_NODELETE)
    with (source/'lifecycle.c').open('a') as stream: stream.write('\\n/* distinct build */\\n')
    second=builder.build(output)
    assert first['buildIdentitySha256']!=second['buildIdentitySha256']
    try: L.LifecycleRuntime.load(output,manifest=second)
    except L.IdentityMismatch as e: assert 'Loaded lifecycle' in str(e)
    else: raise AssertionError('cached old code accepted new report')
""")


if __name__ == '__main__': unittest.main()
