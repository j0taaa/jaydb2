#!/usr/bin/env python3
"""Integration tests execute .so programs inside THIS Python server process.

Fixture emission is primary-only, intentionally separate from production gate.
"""
import ctypes as C
import hashlib
import importlib.util
import json
import locale
import os
import random
import resource
import struct
from contextlib import contextmanager
from decimal import Decimal, localcontext
from pathlib import Path
import re
import subprocess
import tempfile
import threading
import time
import unittest

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location('native_build', ROOT / 'tools/native/build.py')
BUILD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BUILD)
BEND2 = Path(os.environ.get('JAYDB_NATIVE_BEND2', ROOT / '.tools/bend-source-2.0.39/bend2'))


@contextmanager
def unlimited_main_stack():
    previous = resource.getrlimit(resource.RLIMIT_STACK)
    assert previous[1] == resource.RLIM_INFINITY, 'Test environment needs unlimited hard stack limit'
    resource.setrlimit(resource.RLIMIT_STACK, (resource.RLIM_INFINITY, previous[1]))
    try:
        yield
    finally:
        resource.setrlimit(resource.RLIMIT_STACK, previous)


class Request(C.Structure):
    _fields_ = [('abi_version', C.c_uint32), ('flags', C.c_uint32), ('input', C.c_void_p),
                ('input_len', C.c_uint64), ('output', C.c_void_p), ('output_capacity', C.c_uint64),
                ('memory_bytes', C.c_uint64), ('timeout_ns', C.c_uint64),
                ('term_stack_bytes', C.c_uint64), ('native_stack_bytes', C.c_uint64)]


class Result(C.Structure):
    _fields_ = [('status', C.c_uint32), ('runtime_code', C.c_uint32), ('output_len', C.c_uint64),
                ('elapsed_ns', C.c_uint64), ('charged_bytes', C.c_uint64)]


class RequestV2(C.Structure):
    _fields_ = [('base', Request), ('execution_timeout_ns', C.c_uint64), ('preparation_timeout_ns', C.c_uint64)]


class ResultV2(C.Structure):
    _fields_ = [('base', Result), ('stage', C.c_uint32), ('reserved', C.c_uint32),
                ('setup_ns', C.c_uint64), ('execution_ns', C.c_uint64), ('preparation_ns', C.c_uint64)]


class Ns128(C.Structure):
    _fields_ = [('lo', C.c_uint64), ('hi', C.c_uint64)]

    @classmethod
    def natural(cls, value):
        value = min(value, (1 << 128) - 1)
        return cls(value & ((1 << 64) - 1), value >> 64)

    def integer(self):
        return self.lo | (self.hi << 64)


class RequestV3(C.Structure):
    _fields_ = [('abi_version', C.c_uint32), ('flags', C.c_uint32), ('input', C.c_void_p),
                ('input_len', C.c_uint64), ('output_limit', C.c_uint64), ('memory_bytes', C.c_uint64),
                ('term_stack_bytes', C.c_uint64), ('native_stack_bytes', C.c_uint64),
                ('setup_timeout_ns', Ns128), ('execution_timeout_ns', Ns128), ('preparation_timeout_ns', Ns128)]


class ResultV3(C.Structure):
    _fields_ = [('status', C.c_uint32), ('runtime_code', C.c_uint32), ('stage', C.c_uint32),
                ('reserved', C.c_uint32), ('output', C.c_void_p), ('output_len', C.c_uint64),
                ('output_capacity', C.c_uint64), ('lease', C.c_uint64), ('charged_bytes', C.c_uint64),
                ('elapsed_ns', Ns128), ('stage_elapsed_ns', Ns128 * 3), ('preparation_started_ns', Ns128)]


class Module:
    def __init__(self, path):
        self.library = C.CDLL(str(path), mode=os.RTLD_LOCAL | os.RTLD_NOW)
        self.library.jaydb_native_run_v1.argtypes = [C.POINTER(Request), C.POINTER(Result)]
        self.library.jaydb_native_run_v1.restype = C.c_uint32
        self.library.jaydb_native_run_v2.argtypes = [C.POINTER(RequestV2), C.POINTER(ResultV2)]
        self.library.jaydb_native_run_v2.restype = C.c_uint32
        self.library.jaydb_native_preparation_started_v2.restype = C.c_uint64
        self.library.jaydb_native_run_v3.argtypes = [C.POINTER(RequestV3), C.POINTER(ResultV3)]
        self.library.jaydb_native_run_v3.restype = C.c_uint32
        self.library.jaydb_native_run_deadline_v3.argtypes = [C.POINTER(RequestV3), C.POINTER(ResultV3), C.POINTER(Ns128)]
        self.library.jaydb_native_run_deadline_v3.restype = C.c_uint32
        self.library.jaydb_native_release_v3.argtypes = [C.c_uint64]
        self.library.jaydb_native_release_v3.restype = C.c_uint32

    def run(self, data=b'', *, capacity=4096, memory=16 << 20, timeout=1_000_000_000,
            terms=1 << 20, stack=1 << 20, flags=1):
        input_ = C.create_string_buffer(data)
        output = C.create_string_buffer(capacity)
        request = Request(1, flags, C.addressof(input_), len(data), C.addressof(output), capacity,
                          memory, timeout, terms, stack)
        result = Result()
        status = self.library.jaydb_native_run_v1(C.byref(request), C.byref(result))
        assert status == result.status
        return result, output.raw[:result.output_len]

    def run_v2(self, data=b'', *, setup=1_000_000_000, execution=1_000_000_000,
               preparation=1_000_000_000, capacity=4096):
        input_ = C.create_string_buffer(data)
        output = C.create_string_buffer(capacity)
        base = Request(2, 1, C.addressof(input_), len(data), C.addressof(output), capacity,
                       16 << 20, setup, 1 << 20, 1 << 20)
        request = RequestV2(base, execution, preparation)
        result = ResultV2()
        status = self.library.jaydb_native_run_v2(C.byref(request), C.byref(result))
        assert status == result.base.status
        return result, output.raw[:result.base.output_len]

    def run_v3(self, data=b'', *, setup=1_000_000_000, execution=1_000_000_000,
               preparation=1_000_000_000, limit=(1 << 64) - 1, memory=16 << 20,
               terms=1 << 20, stack=1 << 20, release=True, setup_absolute=None):
        input_ = C.create_string_buffer(data)
        request = RequestV3(3, 1, C.addressof(input_), len(data), min(limit, (1 << 64) - 1),
            min(memory, (1 << 64) - 1), terms, stack, Ns128.natural(setup),
            Ns128.natural(execution), Ns128.natural(preparation))
        result = ResultV3()
        if setup_absolute is None:
            status = self.library.jaydb_native_run_v3(C.byref(request), C.byref(result))
        else:
            absolute = Ns128.natural(setup_absolute)
            status = self.library.jaydb_native_run_deadline_v3(C.byref(request), C.byref(result), C.byref(absolute))
        assert status == result.status
        output = C.string_at(result.output, result.output_len) if result.output_len else b''
        if release and result.lease:
            assert self.library.jaydb_native_release_v3(result.lease) == 0
        return result, output


class NativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if not (BEND2 / 'comp.ts').exists():
            raise RuntimeError('Set JAYDB_NATIVE_BEND2 to pinned official bend2 directory')
        cls.temp = tempfile.TemporaryDirectory(prefix='jaydb-native-tests-')
        cls.directory = Path(cls.temp.name)
        cls.cache = {}

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def module(self, fixture, mode='generic'):
        key = fixture, mode
        if key not in self.cache:
            target = self.directory / f'{fixture}-{mode}'
            subprocess.run(['node', str(ROOT / 'tests/native/emit_fixture.mjs'), str(BEND2),
                            str(ROOT / f'tests/native/fixtures/{fixture}.bend'), str(target.with_suffix('.c')), mode],
                           check=True, timeout=30, capture_output=True)
            source = target.with_suffix('.c').read_text()
            read = re.search(r'^#define (CID_\w*native_effects_read) \d+$', source, re.M)[1]
            write_match = re.search(r'^#define (CID_\w*native_effects_write) \d+$', source, re.M)
            write = write_match[1] if write_match else None
            options = {}
            if fixture.startswith('loop'):
                for key, stem in [('loop', 'native_effects_loop'), ('continue', 'native_effects_Continuar'),
                                  ('finish', 'native_effects_Encerrar'), ('inconsistent', 'native_effects_Inconsistente'),
                                  ('prepare', 'native_effects_Preparar')]:
                    matches = re.findall(r'^#define (CID_(?:\w*_)?' + stem + r') \d+$', source, re.M)
                    options[key + '_cid'] = matches[0]
                enter_match = re.search(r'^#define (CID_\w*native_effects_enter) \d+$', source, re.M)
                if enter_match:
                    options['enter_cid'] = enter_match[1]
            BUILD.build_module(target.with_suffix('.c'), target.with_suffix('.so'), input_cid=read,
                               output_cid=write, allow_specialized=mode != 'generic', **options)
            self.cache[key] = Module(target.with_suffix('.so'))
        return self.cache[key]

    def test_binary_echo_and_same_process(self):
        pid = os.getpid()
        module = self.module('echo')
        result, output = module.run(bytes(range(256)), capacity=256)
        self.assertEqual((result.status, output), (0, bytes(range(256))))
        self.assertEqual(pid, os.getpid())

    def test_trusted_loop_with_closed_static_step(self):
        result, output = self.module('loop').run_v2(bytes([1, 2, 3, 0, 4, 5]))
        self.assertEqual((result.base.status, output), (0, bytes([5, 4, 3, 2, 1])))
        self.assertEqual(result.stage, 2)
        self.assertGreater(result.execution_ns, 0)
        self.assertGreater(result.preparation_ns, 0)

    def test_loop_inconsistent_is_internal_failure(self):
        result, output = self.module('loop').run_v2(bytes([255]))
        self.assertEqual((result.base.status, output), (12, b''))

    def test_loop_repeated_prepare_cannot_renew_deadline(self):
        result, output = self.module('loop').run_v2(bytes([0, 0]))
        self.assertEqual((result.base.status, output), (12, b''))

    def test_loop_execution_and_preparation_have_separate_deadlines(self):
        module = self.module('loop')
        result, _ = module.run_v2(b'123', execution=1)
        self.assertEqual((result.base.status, result.stage), (3, 1))
        result, _ = module.run_v2(b'\x00abc', preparation=1)
        self.assertEqual((result.base.status, result.stage), (3, 2))
        result, output = module.run_v2(b'\x01\x00\x02')
        self.assertEqual((result.base.status, output), (0, b'\x02\x01'))

    def test_loop_rejects_captured_step(self):
        result, output = self.module('loop_captured').run_v2(b'secret')
        self.assertEqual((result.base.status, output), (13, b''))

    def test_enter_before_initial_and_loop_keeps_execution_stage(self):
        result, output = self.module('loop_enter').run_v2(b'\x01\x00\x02')
        self.assertEqual((result.base.status, output, result.stage), (0, b'\x02\x01', 2))
        result, _ = self.module('loop_enter').run_v2(b'\x01', execution=1)
        self.assertEqual((result.base.status, result.stage), (3, 1))

    def test_loop_accepts_actual_execucao_state_layout(self):
        result, output = self.module('loop_execucao').run_v2()
        self.assertEqual((result.base.status, output), (0, bytes([7, 0, 255])))

    def test_maximum_u64_timeouts_do_not_reject_small_calls(self):
        maximum = (1 << 64) - 1
        result, output = self.module('echo').run(b'large deadline', timeout=maximum)
        self.assertEqual((result.status, output), (0, b'large deadline'))
        result, output = self.module('loop_enter').run_v2(b'\x01\x00\x02', setup=maximum,
                                                        execution=maximum, preparation=maximum)
        self.assertEqual((result.base.status, output), (0, b'\x02\x01'))

    def test_empty_and_repeat(self):
        module = self.module('echo')
        for value in [b'', b'\x00\xff\xc0\x80', b'a' * 65536, b'repeated']:
            result, output = module.run(value, capacity=len(value))
            self.assertEqual((result.status, output), (0, value))

    def test_limits_and_recovery(self):
        module = self.module('echo')
        for kwargs, status in [({'memory': 1 << 20}, 4), ({'timeout': 1}, 3),
                               ({'capacity': 1}, 7), ({'flags': 0}, 1),
                               ({'terms': 4096, 'memory': 4 << 20}, 0)]:
            result, output = module.run(b'\x00\xff', **kwargs)
            self.assertEqual(result.status, status)
            if status:
                self.assertEqual((result.output_len, output), (0, b''))
            result, output = module.run(b'published-state-remains-host-owned')
            self.assertEqual((result.status, output), (0, b'published-state-remains-host-owned'))

    def test_real_heap_limit(self):
        module = self.module('echo')
        result, _ = module.run(b'x' * 65536, capacity=65536, memory=3 << 20)
        self.assertEqual(result.status, 4)
        self.assertEqual(result.runtime_code, 0)

    def test_nat_math(self):
        result, output = self.module('nat_math').run()
        self.assertEqual((result.status, output), (0, bytes([221, 128, 96, 7, 11, 13, 4])))

    def test_real_configuration_nat_is_compact(self):
        # These are the exact configuration magnitudes, never a reduced test
        # configuration. Both eager constructions must now finish compactly.
        for fixture in ['nat_config_used', 'nat_config_unused']:
            module = self.module(fixture)
            result, output = module.run(timeout=1_000_000_000, memory=4 << 20)
            self.assertEqual((result.status, result.runtime_code, output), (0, 0, b'\x01'))

    def test_absolute_preparation_epoch_getter(self):
        module = self.module('loop_enter')
        before = time.monotonic_ns()
        result, output = module.run_v2(b'\x01\x00\x02')
        epoch = module.library.jaydb_native_preparation_started_v2()
        after = time.monotonic_ns()
        self.assertEqual((result.base.status, output, result.stage), (0, b'\x02\x01', 2))
        self.assertLessEqual(before, epoch)
        self.assertLessEqual(epoch, after)
        self.assertLessEqual(result.preparation_ns, after - epoch)
        self.assertEqual(module.library.jaydb_native_preparation_started_v2(), epoch)
        result, _ = module.run_v2(b'\x01', execution=1)
        self.assertEqual((result.base.status, result.stage), (3, 1))
        self.assertEqual(module.library.jaydb_native_preparation_started_v2(), 0)
        result, _ = module.run_v2(b'\x00', preparation=1)
        self.assertEqual((result.base.status, result.stage), (3, 2))
        self.assertGreater(module.library.jaydb_native_preparation_started_v2(), 0)
        module.run(b'\x00')
        self.assertEqual(module.library.jaydb_native_preparation_started_v2(), 0)

    def nat_result(self, op, a, b=0):
        data = bytes([op]) + str(a).encode() + b'\xff' + str(b).encode()
        result, output = self.module('nat_arithmetic').run(data, timeout=10_000_000_000)
        self.assertEqual((result.status, result.runtime_code), (0, 0), (op, a, b))
        return output.decode()

    def test_nat_arbitrary_precision_and_patterns(self):
        values = [0, 1, 2, 3, (1 << 32) - 1, 1 << 32, (1 << 48) + 1,
                  (1 << 56) - 1, 1 << 56, (1 << 64) - 1, 1 << 64, (1 << 161) + 7]
        for a in values:
            self.assertEqual(self.nat_result(7, a), ['zero', 'one', 'two'][a] if a < 3 else str(a - 3))
            self.assertEqual(self.nat_result(11, a), str(a & 0xffffffff))
        rng = random.Random(0x4E4154)
        pairs = [(a, values[-i - 1]) for i, a in enumerate(values)]
        pairs += [(rng.getrandbits(rng.randint(1, 256)), rng.getrandbits(rng.randint(1, 192)))
                  for _ in range(35)]
        for a, b in pairs:
            expected = [a + b, max(0, a - b), a * b, a // b if b else 0, a % b if b else a]
            for op, value in enumerate(expected):
                self.assertEqual(self.nat_result(op, a, b), str(value))
            self.assertEqual(self.nat_result(5, a, b), f'{expected[3]}:{expected[4]}')
            self.assertEqual(self.nat_result(6, a, b), '<' if a < b else '>' if a > b else '=')
        for a, b in [(0, 0), (0, 500), (1, 1 << 160), (2, 180), (123, 17), ((1 << 65) - 1, 3)]:
            self.assertEqual(self.nat_result(8, a, b), str(pow(a, b)))
        for a, b in [(1 << 120, (1 << 130) + 7), (1 << 64, 1 << 64), (0, 1 << 90)]:
            self.assertEqual(self.nat_result(9, a, b), str(min(a, b)))
            self.assertEqual(self.nat_result(10, a, b), str(max(a, b)))
            self.assertEqual(self.nat_result(15, a, b), str(a + b))
        for a, b in [(3, 0), (3, 31), (3, 32), ((1 << 89) + 123, 1 << 90)]:
            self.assertEqual(self.nat_result(12, a, b), str(pow(a & 0xffffffff, b, 1 << 32)))
            self.assertEqual(self.nat_result(13, a, b), str(((a & 0xffffffff) << b) & 0xffffffff) if b < 32 else '0')
            self.assertEqual(self.nat_result(14, a, b), str((a & 0xffffffff) >> b) if b < 32 else '0')

    def test_compact_nat_in_native_loop_state(self):
        result, output = self.module('loop_nat').run_v2()
        self.assertEqual((result.base.status, result.stage, output), (0, 2, b'\x01'))

    def test_nat_chunk_carries_division_gc_and_immortal_refs(self):
        module = self.probe_module('nat-chunks', '''
static void nat_chunks_probe(Env e) {
  Term a = jaydb_nat_new(e, 130);
  for (u64 i = 0; i < 130; ++i) jaydb_nat_put(e, a, i, UINT32_MAX);
  a = term_keep(e, a, 1);
  Term next = jaydb_nat_succ(e, a);
  if (jaydb_nat_length(e, next) != 131 || jaydb_nat_get(e, next, 130) != 1)
    jaydb_abort(JAYDB_RUNTIME, 101);
  for (u64 i = 0; i < 130; ++i)
    if (jaydb_nat_get(e, next, i)) jaydb_abort(JAYDB_RUNTIME, 102);
  a = term_keep(e, a, 1);
  if (jaydb_nat_sub(e, next, a) != JAYDB_NAT_SMALL(1)) jaydb_abort(JAYDB_RUNTIME, 103);
  a = term_keep(e, a, 2);
  Term product = jaydb_nat_mul(e, a, a);
  for (u64 i = 0; i < 260; ++i) {
    u32 want = i == 0 ? 1 : i < 130 ? 0 : i == 130 ? UINT32_MAX - 1 : UINT32_MAX;
    if (jaydb_nat_get(e, product, i) != want) jaydb_abort(JAYDB_RUNTIME, 104);
  }
  a = term_keep(e, a, 1);
  Term q, r;
  jaydb_nat_divmod(e, product, a, &q, &r);
  if (!jaydb_nat_is_zero(r) || jaydb_nat_cmp(e, q, a) != 1)
    jaydb_abort(JAYDB_RUNTIME, 105);
  u64 start = jaydb_heap_next;
  for (u64 i = 0; i < 500; ++i) {
    Term n = jaydb_nat_new(e, 130);
    jaydb_nat_put(e, n, 129, 1);
    u64 cell = heap_alloc(e, 1);
    e.mem[cell] = n;
    e.mem[cell + 1] = term_pak(CID_Nil, 0);
    term_drop(e, term_ctr(CID_Con, cell));
  }
  if (jaydb_heap_next > start + 1024) jaydb_abort(JAYDB_RUNTIME, 106);
  Term n = jaydb_nat_new(e, 130);
  jaydb_nat_put(e, n, 129, 1);
  n = rfc_seal(e, n);
  rfc_bump(e, term_loc(n), RFC_CNT);
  for (u32 i = 0; i < 8; ++i) term_drop(e, n);
  if (jaydb_nat_length(e, n) != 130 || jaydb_nat_get(e, n, 129) != 1)
    jaydb_abort(JAYDB_RUNTIME, 107);
}
''', '    nat_chunks_probe(e);')
        result, output = module.run(b'chunks', timeout=10_000_000_000)
        self.assertEqual((result.status, result.runtime_code, output), (0, 0, b'chunks'))

    def test_nat_arithmetic_safe_points_and_recovery(self):
        for name, operation in [('mul', '(void)jaydb_nat_mul(e, a, b);'),
                                ('div', 'Term q, r; jaydb_nat_divmod(e, a, b, &q, &r);')]:
            module = self.probe_module('nat-time-' + name, '''
static u32 nat_phase;
__attribute__((visibility("default"))) u32 nat_probe_phase(void) { return nat_phase; }
static void nat_slow_probe(Env e) {
  if (nat_phase) return;
  Term a = jaydb_nat_new(e, 8192), b = jaydb_nat_new(e, 4096);
  for (u64 i = 0; i < 8192; ++i) jaydb_nat_put(e, a, i, UINT32_MAX);
  for (u64 i = 0; i < 4096; ++i) jaydb_nat_put(e, b, i, UINT32_MAX);
  nat_phase = 1;
  jaydb_active->deadline = jaydb_clock() + 2000000;
''' + operation + '\n}\n', '    nat_slow_probe(e);')
            result, output = module.run(timeout=5_000_000_000)
            self.assertEqual((result.status, output), (3, b''))
            self.assertEqual(module.library.nat_probe_phase(), 1)
            result, output = module.run(b'recovered')
            self.assertEqual((result.status, output), (0, b'recovered'))

    def test_nat_arena_limit_and_recovery(self):
        module = self.probe_module('nat-memory', '''
static u32 nat_allocated;
static void nat_memory_probe(Env e) {
  if (nat_allocated++) return;
  (void)jaydb_nat_new(e, jaydb_heap_words);
}
''', '    nat_memory_probe(e);')
        result, output = module.run(timeout=5_000_000_000)
        self.assertEqual((result.status, result.runtime_code, output), (4, 0, b''))
        result, output = module.run(b'recovered')
        self.assertEqual((result.status, output), (0, b'recovered'))

    def test_parallel_let_runs_sequentially(self):
        result, output = self.module('parallel').run()
        self.assertEqual((result.status, output), (0, bytes([13, 13])))

    def test_f32_show(self):
        result, output = self.module('f32_show').run()
        self.assertEqual((result.status, output), (0, b'1.25'))

    def f32_harness(self):
        if 'f32-harness' not in self.cache:
            obj = self.directory / 'f32-harness.o'
            common = [BUILD.CLANG, '-O2', '-fPIC', '-I', str(ROOT / 'native')]
            coverage = ['-fsanitize-coverage=trace-pc-guard,bb,no-prune']
            source = ROOT / 'tests/native/f32_harness.c'
            ir = self.directory / 'f32-harness.ll'
            subprocess.run([*common, *coverage, '-S', '-emit-llvm', str(source), '-o', str(ir)], check=True)
            self.assertEqual(BUILD.audit_ir(ir.read_text())['unpolledCycles'], 0)
            subprocess.run([*common, *coverage, '-c', str(source), '-o', str(obj)], check=True)
            guard = self.directory / 'f32-guard.o'
            subprocess.run([*common, '-c', str(ROOT / 'native/guard.c'), '-o', str(guard)], check=True)
            target = self.directory / 'f32-harness.so'
            subprocess.run([BUILD.CLANG, '-shared', '-Wl,-z,defs,-Bsymbolic', str(obj), str(guard),
                            '-lm', '-o', str(target)], check=True)
            harness = C.CDLL(str(target))
            for name in ['reference', 'streaming']:
                getattr(harness, name).argtypes = [C.c_char_p, C.c_uint64]
                getattr(harness, name).restype = C.c_uint64
            harness.timed.argtypes = [C.c_char_p, C.c_uint64, C.c_uint64]
            harness.timed.restype = C.c_uint32
            self.cache['f32-harness'] = harness
        return self.cache['f32-harness']

    def assert_f32_equivalent(self, values):
        harness = self.f32_harness()
        for value in values:
            if isinstance(value, str):
                value = value.encode()
            self.assertEqual(harness.streaming(value, len(value)), harness.reference(value, len(value)),
                             repr(value[:200]) + f' ({len(value)} bytes)')

    def test_f32_read_streaming_abi_and_strings(self):
        module = self.module('f32_read')
        harness = self.f32_harness()
        values = [b'', b'1.25', b'-0', b'+inf', b'-INFINITY', b'-NaN', b'\t\v\r\n 1.5',
                  b'.5', b'1.', b'1e+', b'1 ', b'0x1p0', b'nan(123)', b'1\x00',
                  b'1\xff', b'\xc2\xa0' + b'1', b'1' + b'0' * 20000 + b'e-20000',
                  b'1.' + b'0' * 20000 + b'1', b'1e-' + b'0' * 20000 + b'1']
        for value in values:
            result, output = module.run(value, timeout=5_000_000_000)
            expected = harness.reference(value, len(value))
            self.assertEqual(result.status, 0, repr(value[:60]))
            self.assertEqual(output, b'\x01' + struct.pack('<I', expected & 0xffffffff)
                             if expected else b'\x00', repr(value[:60]))
        result, output = module.run(b'1.25', timeout=1)
        self.assertEqual((result.status, output), (3, b''))
        result, output = module.run(b'1.25')
        self.assertEqual((result.status, output), (0, b'\x01\x00\x00\xa0\x3f'))

    def test_f32_lexical_semantics_and_arbitrary_bytes(self):
        values = ['', ' ', '+', '-', '.', '.e1', '+.0', '000', '0e9999999999', '-0e-99999999',
                  'INF', 'Infinity', '-inf', '+NaN', 'nan()', 'nan(payload)', '0X1.2p3',
                  '0x0', '1_0', '1,5', 'infi', 'infinityx', 'nan ', '1e2junk', '1e--2',
                  '1E+2', '\u20031', '１２', '\ufeff1']
        values += [bytes([i]) + b'1' for i in range(256)]
        values += [b'1' + bytes([i]) for i in range(256)]
        values += [b'\x00', b'1\x00' + b'0' * 10000]
        self.assert_f32_equivalent(values)

    def test_f32_unicode_invalid_chars_and_shared_string(self):
        module = self.module('f32_unicode')
        for value, flags in [(b'1.25', b'\x01\x01'), (b'invalid', b'\x00\x00')]:
            result, output = module.run(value)
            self.assertEqual((result.status, output), (0, flags + b'\x00' * 7))

    def test_f32_rounding_boundaries_all_modes(self):
        # Exact values and halfway points from zero through overflow, including
        # binade changes and even/odd ties. A decisive digit may be arbitrarily
        # far beyond the retained prefix; zero tails must remain exact ties.
        with localcontext() as context:
            context.prec = 1200
            values = []
            for bits in [0, 1, 2, 3, 0x007ffffe, 0x007fffff, 0x00800000,
                         0x3effffff, 0x3f000000, 0x3f7fffff, 0x3f800000, 0x3f800001,
                         0x4affffff, 0x4b000000, 0x7f7ffffe, 0x7f7fffff]:
                lower = Decimal(struct.unpack('<f', struct.pack('<I', bits))[0])
                upper = Decimal(2) ** 128 if bits == 0x7f7fffff else Decimal(
                    struct.unpack('<f', struct.pack('<I', bits + 1))[0])
                for boundary in [lower, (lower + upper) / 2]:
                    for x in [boundary, boundary - Decimal('1e-1000'), boundary + Decimal('1e-1000')]:
                        s = format(x, 'f')
                        values.extend([s, '-' + s if not s.startswith('-') else s[1:]])
            values += ['1e999999999999999999', '-1e999999999999999999',
                       '1e-999999999999999999', '-1e-999999999999999999']
        libm = C.CDLL('libm.so.6')
        original = libm.fegetround()
        try:
            for mode in [0, 0x400, 0x800, 0xc00]:  # Linux x86_64 fenv.h
                self.assertEqual(libm.fesetround(mode), 0)
                self.assert_f32_equivalent(values)
        finally:
            libm.fesetround(original)

    def test_f32_long_exponents_cancellation_and_sticky(self):
        size = 100000
        self.assert_f32_equivalent([
            b'1' + b'0' * size + f'e-{size}'.encode(),
            b'0.' + b'0' * size + b'1' + f'e{size + 1}'.encode(),
            b'1.000000059604644775390625' + b'0' * size,
            b'1.000000059604644775390625' + b'0' * size + b'1',
            b'1.000000059604644775390624' + b'9' * size,
            b'1e' + b'0' * size + b'2', b'1e-' + b'9' * size,
            b'0e' + b'9' * size, b' ' * size + b'1',
        ])

    def test_f32_differential_randomized(self):
        rng = random.Random(0xF32039)
        values = []
        for _ in range(4000):
            digits = ''.join(rng.choices('0123456789', k=rng.randint(1, 700)))
            position = rng.randrange(len(digits) + 1)
            values.append(rng.choice(['', '+', '-']) + digits[:position] + '.' + digits[position:]
                          + rng.choice(['e', 'E']) + str(rng.randint(-900, 900)))
        for _ in range(1000):
            values.append(bytes(rng.choices(b'0123456789.eE+-inxNaIf() \t\x00\xff', k=rng.randint(0, 80))))
        self.assert_f32_equivalent(values)

    def test_f32_locale_decimal_comma_and_multibyte(self):
        original_path = os.environ.get('LOCPATH')
        original_locale = locale.setlocale(locale.LC_NUMERIC)
        try:
            for name, radix in [('jaydb_comma', ','), ('jaydb_multibyte', '\u066b')]:
                source = self.directory / (name + '.locale')
                categories = ['CTYPE', 'COLLATE', 'TIME', 'MONETARY', 'MESSAGES', 'PAPER',
                              'NAME', 'ADDRESS', 'TELEPHONE', 'MEASUREMENT', 'IDENTIFICATION']
                source.write_text('\n'.join(f'LC_{c}\ncopy "en_US"\nEND LC_{c}' for c in categories)
                                  + f'\nLC_NUMERIC\ndecimal_point "<U{ord(radix):04X}>"\n'
                                  + 'thousands_sep ""\ngrouping -1\nEND LC_NUMERIC\n')
                subprocess.run(['localedef', '--no-archive', '-f', 'UTF-8', '-i', str(source),
                                str(self.directory / name)], check=True, capture_output=True, timeout=10)
                os.environ['LOCPATH'] = str(self.directory)
                locale.setlocale(locale.LC_NUMERIC, name)
                self.assertEqual(locale.localeconv()['decimal_point'], radix)
                self.assert_f32_equivalent(['1' + radix + '25', radix + '5', '1' + radix,
                                           '1.25', '1,25', '1' + radix + 'e2', '1e-20', '-INF',
                                           '1' + radix + '0' * 300 + '1'])
        finally:
            locale.setlocale(locale.LC_NUMERIC, original_locale)
            if original_path is None:
                os.environ.pop('LOCPATH', None)
            else:
                os.environ['LOCPATH'] = original_path

    def test_f32_scanner_timeout_and_recovery(self):
        harness = self.f32_harness()
        tail = b'0' * (8 << 20)
        # Normal scan, rejected-string drain, leading whitespace and exponent.
        for value in [b'1.' + tail + b'1', b'junk' + tail,
                      b' ' * len(tail) + b'1', b'1e-' + tail + b'1']:
            started = time.monotonic()
            self.assertEqual(harness.timed(value, len(value), 2_000_000), 3)
            self.assertLess(time.monotonic() - started, 1)
        self.assert_f32_equivalent([b'1.25', b'-0', b'1e-45'])

    def test_array_depth32(self):
        result, output = self.module('array32').run()
        self.assertEqual((result.status, output), (0, b'\x20'))

    def test_specialized_array_is_representation_error(self):
        result, _ = self.module('array_new32', 'official').run()
        self.assertEqual((result.status, result.runtime_code), (9, 8))

    def test_specialized_unbalanced_array_rejects_valid_tree(self):
        result, _ = self.module('array32', 'official').run()
        self.assertEqual((result.status, result.runtime_code), (11, 2))

    def probe_module(self, name, definitions, statements):
        self.module('echo')
        source = (self.directory / 'echo-generic.c').read_text()
        source = source.replace('// Segments\n// ========', definitions + '\n// Segments\n// ========')
        source = source.replace('WL_CASE(FID_main)\n', 'WL_CASE(FID_main)\n' + statements + '\n')
        target = self.directory / name
        target.with_suffix('.c').write_text(source)
        read = re.search(r'^#define (CID_\w*native_effects_read) \d+$', source, re.M)[1]
        write = re.search(r'^#define (CID_\w*native_effects_write) \d+$', source, re.M)[1]
        BUILD.build_module(target.with_suffix('.c'), target.with_suffix('.so'), input_cid=read, output_cid=write)
        return Module(target.with_suffix('.so'))

    def test_actual_refcount_saturation_and_immortal_drop(self):
        module = self.probe_module('refcount', '''
static void refcount_probe(Env e) {
  u64 loc = heap_alloc(e, 1);
  e.mem[loc] = 42;
  e.mem[loc + 1] = term_pak(CID_Nil, 0);
  Term t = rfc_wrap(e, term_ctr(CID_Con, loc), 1);
  for (u32 i = 0; i < RFC_CNT + 8; ++i) term_keep(e, t, 1);
  u64 redirect = term_loc(t);
  if ((e.mem[redirect] & RFC_CNT) != RFC_CNT || term_peek(e.mem, t) != loc)
    jaydb_abort(JAYDB_RUNTIME, 91);
  for (u32 i = 0; i < 16; ++i) term_drop(e, t);
  Term fields[2];
  u64 spare = ctr_take(e, t, 2, fields);
  if (spare || fields[0] != 42 || fields[1] != term_pak(CID_Nil, 0)
      || (e.mem[redirect] & RFC_CNT) != RFC_CNT || term_peek(e.mem, t) != loc)
    jaydb_abort(JAYDB_RUNTIME, 92);
}
''', '    refcount_probe(e);')
        result, output = module.run(b'kept', timeout=10_000_000_000)
        self.assertEqual((result.status, output), (0, b'kept'))

    def test_machine_word_ids_survive_terms_heap_and_refcount_masks(self):
        module = self.probe_module('word-ids', '''
static void word_ids_probe(Env e) {
  const u64 ids[] = { 0, 65535, 65536, 4294967295ull, 4294967296ull,
                     0xFEDCBA9876543210ull, UINT64_MAX };
  u64 loc = heap_alloc(e, 1);
  for (u32 i = 0; i < sizeof ids / sizeof *ids; ++i) {
    for (u64 tag = TAG_PAK; tag <= TAG_ARR; ++tag) {
      Term t = term_make(tag, ids[i], loc);
      e.mem[loc] = t;
      if (term_aux(e.mem[loc]) != ids[i] || term_tag(t) != tag
          || term_loc(t) != loc || term_rfc(t)) jaydb_abort(JAYDB_RUNTIME, 101);
    }
    // Synthetic metadata tests do not dereference a nonexistent CID table row.
    // Real constructor/table dispatch is checked in admitted and relocated C.
    Term t = rfc_wrap(e, term_ctr(ids[i], loc), 1);
    if (term_aux(t) != ids[i] || term_tag(t) != TAG_CTR || !term_rfc(t)
        || term_peek(e.mem, t) != loc) jaydb_abort(JAYDB_RUNTIME, 102);
    term_keep(e, t, 2);
    term_drop(e, t); // still shared: no CID table access
    if (term_aux(t) != ids[i] || (e.mem[term_loc(t)] & RFC_CNT) != 2)
      jaydb_abort(JAYDB_RUNTIME, 103);
    Term restored = (t & ~(Term)(RFC_BIT | LOC_MASK)) | term_peek(e.mem, t);
    if (restored != term_ctr(ids[i], loc)) jaydb_abort(JAYDB_RUNTIME, 104);
    heap_free(e, 0, term_loc(t));
  }
  heap_free(e, 1, loc);
}
''', '    word_ids_probe(e);')
        result, output = module.run(b'full metadata word')
        self.assertEqual((result.status, output), (0, b'full metadata word'))

    def relocated_module(self, fixture):
        # Runtime probe, not a new admitted Book: relocate ALL table rows past
        # the old boundary, including closures, saved FIDs and effect CIDs.
        self.module(fixture)
        source = (self.directory / f'{fixture}-generic.c').read_text()
        definitions = re.findall(r'^#define ([CF]ID_\w+) (\d+)$', source, re.M)
        for prefix, table in [('FID_', 'Fid FID_T'), ('CID_', 'Cid CID_T')]:
            symbols = [name for name, _ in definitions if name.startswith(prefix)]
            match = re.search(r'(CONSTV ' + table + r'\[\] = \{ )(.*?)( \};)', source)
            rows = re.findall(r'\{[^{}]*\}', match[2])
            self.assertLessEqual(len(rows), len(symbols))
            source = source[:match.start(2)] + ', '.join(
                f'[{symbol}] = {row}' for symbol, row in zip(symbols, rows)) + source[match.end(2):]
        source = source.replace('#define WL_X(F) WL_##F,', '#define WL_X(F) [F] = WL_##F,')
        source = re.sub(r'^(#define [CF]ID_\w+) (\d+)$',
                        lambda m: f'{m[1]} {int(m[2]) + 65534}', source, flags=re.M)
        target = self.directory / f'{fixture}-relocated'
        target.with_suffix('.c').write_text(source)
        def cid(stem):
            match = re.search(r'^#define (CID_\w*native_effects_' + stem + r') \d+$', source, re.M)
            return match[1] if match else None
        options = {}
        if fixture.startswith('loop'):
            options = {key + '_cid': cid(stem) for key, stem in [
                ('loop', 'loop'), ('continue', 'Continuar'), ('prepare', 'Preparar'),
                ('finish', 'Encerrar'), ('inconsistent', 'Inconsistente')]}
        BUILD.build_module(target.with_suffix('.c'), target.with_suffix('.so'),
                           input_cid=cid('read'), output_cid=cid('write'), **options)
        return Module(target.with_suffix('.so'))

    def test_relocated_cid_fid_tables_loop_and_captured_step(self):
        module = self.relocated_module('loop')
        result, output = module.run_v2(b'\x01\x02\x00\x03')
        self.assertEqual((result.base.status, result.stage, output), (0, 2, b'\x03\x02\x01'))
        result, _ = module.run_v2(b'\xff')
        self.assertEqual(result.base.status, 12)
        result, output = module.run_v2(b'\x00')
        self.assertEqual((result.base.status, output), (0, b''))
        result, output = self.relocated_module('loop_captured').run_v2(b'\x01')
        self.assertEqual((result.base.status, output), (13, b''))

    def test_relocated_tables_with_nat_captures_and_gc(self):
        module = self.relocated_module('nat_arithmetic')
        a, b = (1 << 160) + 17, (1 << 96) + 3
        for op, expected in [(0, a + b), (2, a * b), (15, a + b)]:
            data = bytes([op]) + str(a).encode() + b'\xff' + str(b).encode()
            result, output = module.run(data, timeout=10_000_000_000)
            self.assertEqual((result.status, output), (0, str(expected).encode()))

    def admitted_ids(self, count, mode='generic'):
        target = self.directory / f'ids-{count}-{mode}'
        env = {**os.environ, 'JAYDB_BEND_SOURCE': str(BEND2.parent)}
        completed = subprocess.run(['node', str(ROOT / 'tests/native/ids_gate.mjs'),
                                    str(target.with_suffix('.c')), str(count), mode],
                                   capture_output=True, text=True, timeout=60, env=env)
        self.assertEqual(completed.returncode, 0, completed.stderr[-4000:])
        report = json.loads(target.with_suffix('.c.gate.json').read_text())
        self.assertTrue(report['primary'] and report['bendtt'])
        self.assertEqual(report['targets'], ['Bindings:certificado', 'Bindings:termina'])
        if mode == 'official':
            return report, None, None
        self.assertTrue(report['sameCheckedBook'])
        source = target.with_suffix('.c').read_text()
        build = BUILD.build_module(target.with_suffix('.c'), target.with_suffix('.so'),
                                   input_cid='CID_Native_read', output_cid='CID_Native_write')
        self.assertTrue(build['wideIds'])
        self.assertEqual(build['termBytes'], 24)
        return report, Module(target.with_suffix('.so')), source

    def test_admitted_id_counterexample_and_same_book_emission(self):
        original, _, _ = self.admitted_ids(65537, 'official')
        self.assertFalse(original['emitted'])
        self.assertEqual((original['errorCode'], original['error']), ('COMPILE', 'an id over 65535'))
        report, module, source = self.admitted_ids(65537)
        self.assertEqual(report['manySourceSha256'], original['manySourceSha256'])
        self.assertEqual(report['sourceSetSha256'], original['sourceSetSha256'])
        for effect in ['read', 'write']:
            self.assertGreater(int(re.search(r'^#define CID_Native_' + effect + r' (\d+)$', source, re.M)[1]), 65535)
        result, output = module.run(memory=4 << 20)
        self.assertEqual((result.status, output), (0, b'\xf1'))
        for value in range(256):
            result, output = module.run(bytes([value]), memory=4 << 20)
            self.assertEqual((result.status, output), (0, bytes([value ^ 128])))
        for value in [0, 1, 127, 128, 255]:
            result, output = module.run_v3(bytes([value]), memory=4 << 20)
            self.assertEqual((result.status, output), (0, bytes([value ^ 128])))
        result, _ = module.run(timeout=1)
        self.assertEqual(result.status, 3)
        result, output = module.run(b'\x7f', memory=4 << 20)
        self.assertEqual((result.status, output), (0, b'\xff'))

    def test_admitted_id_boundary_65535_65536(self):
        for count, maximum in [(65512, 65535), (65513, 65536)]:
            with self.subTest(maximum=maximum):
                _, module, source = self.admitted_ids(count)
                self.assertEqual(max(map(int, re.findall(r'^#define CID_\w+ (\d+)$', source, re.M))), maximum)
                result, output = module.run(b'\xaa', memory=4 << 20)
                self.assertEqual((result.status, output), (0, b'\x2a'))

    def test_real_free_configuration_initialize_uses_pointer_register_bank(self):
        # Integration regression reported by the controller: Livre.configuracao
        # has 16 flattened fields. Its real initialize Book used to hit two
        # Clang19 register allocation failures with scalar 128-bit arguments.
        import sys
        sys.path.insert(0, str(ROOT))
        from tools.bootstrap import LOCK
        from tools.service.staging import Environment
        from tools.service.abi import Module as ServiceModule
        folder = ROOT / 'examples/credenciais'
        environment = Environment(folder / 'Configuration.bend', folder / 'Seed.bend')
        target = self.directory / 'real-initialize'
        target.mkdir()
        runtime = environment.materialize_tooling(target / 'runtime')
        environment.stage(target, 'initialize')
        emitted = target / 'checked.c'
        resources = target / 'compiler-resources.json'
        resources.write_text(json.dumps({'deadline_ns': str(time.monotonic_ns() + 120_000_000_000)}))
        command = ['node', str(runtime / 'tools/service/compile.mjs'), str(target / 'manifest.json'),
                   str(emitted), str(BEND2.parent),
                   str(ROOT / '.tools' / ('bendtt-' + LOCK['kernelSha256'])), str(resources)]
        result = subprocess.run(command, capture_output=True, text=True, timeout=120)
        error = Path(str(emitted) + '.error.json')
        self.assertEqual(result.returncode, 0, error.read_text() if error.exists() else result.stderr[-4000:])
        build = BUILD.build_module(emitted, target / 'initialize.so', input_cid=None,
                                   output_cid='CID_Native_write')
        self.assertEqual(build['registerBank'], 'charged-term-stack')
        self.assertTrue(build['automaticNativeStackV3'])
        metadata = json.loads(Path(str(emitted) + '.json').read_text())
        from tools.service.build_loading import build as build_loading
        from tools.service.loading import Runtime as LoadingRuntime
        from tests.service.runtime_profile import fixture_lifecycle
        loader=target/'loading.so'
        loading=LoadingRuntime.load(loader,manifest=build_loading(loader))
        module = ServiceModule(target / 'initialize.so',
            loading_runtime=loading,lifecycle_runtime=fixture_lifecycle(loading))
        try:
            # Match the trusted controller environment, without changing the
            # public memory/output/time budgets from the configuration.
            with unlimited_main_stack():
                output = module.run(b'', capacity=int(metadata['limits']['estado']) + 1,
                                    memory=int(metadata['limits']['memoria']),
                                    timeout_ns=int(metadata['limits']['verificacao']))
        finally:
            module.close()
        self.assertEqual(output[0], 1)
        self.assertIn(b'alice', output)
        self.assertIn(b'demo', output)
        result, owned = Module(target / 'initialize.so').run_v3(
            limit=int(metadata['limits']['estado']) + 1, memory=int(metadata['limits']['memoria']),
            setup=int(metadata['limits']['verificacao']), terms=8 << 20, stack=8 << 20)
        self.assertEqual((result.status, owned), (0, output))

    def test_disabled_input_binding_is_explicit(self):
        self.module('echo')
        target = self.directory / 'disabled-input.so'
        source = (self.directory / 'echo-generic.c').read_text()
        output = re.search(r'^#define (CID_\w*native_effects_write) \d+$', source, re.M)[1]
        BUILD.build_module(self.directory / 'echo-generic.c', target,
                           input_cid=None, output_cid=output)
        result, data = Module(target).run(b'not authorized by a numeric sentinel')
        self.assertEqual((result.status, data), (6, b''))

    def arity_source(self, count, mode='generic'):
        target = self.directory / f'arity-{count}-{mode}.c'
        if not target.with_suffix('.c.gate.json').exists():
            result = subprocess.run(['node', str(ROOT / 'tests/native/arity_gate.mjs'),
                                     str(target), str(count), mode], capture_output=True, text=True,
                                    timeout=60, env={**os.environ, 'JAYDB_BEND_SOURCE': str(BEND2.parent)})
            self.assertEqual(result.returncode, 0, result.stderr[-5000:])
        report = json.loads(target.with_suffix('.c.gate.json').read_text())
        self.assertTrue(report['primary'] and report['bendtt'])
        return target, report

    def test_admitted_arity_counterexample_and_boundaries(self):
        _, before = self.arity_source(248, 'official')
        self.assertEqual((before['emitted'], before['error']), (False, 'an arity over 247'))
        for count in [246, 247, 248, 255, 256, 257, 512]:
            with self.subTest(capturedFields=count):
                source, report = self.arity_source(count)
                self.assertTrue(report['sameCheckedBook'])
                if count == 248:
                    self.assertEqual(report['sourceSetSha256'], before['sourceSetSha256'])
                build = BUILD.build_module(source, source.with_suffix('.so'),
                                           input_cid='CID_Native_read', output_cid='CID_Native_write')
                self.assertTrue(build['wordArity'])
                self.assertGreaterEqual(build['registerWords'], count + 1)
                module = Module(source.with_suffix('.so'))
                for x in [0, 1, 17, 127, 255]:
                    result, output = module.run(bytes([x]), memory=4 << 20)
                    expected = (count * x + count * (count - 1) // 2 + 3) % 256
                    self.assertEqual((result.status, output), (0, bytes([expected])))
                    result, output = module.run_v3(bytes([x]), memory=4 << 20)
                    self.assertEqual((result.status, output), (0, bytes([expected])))

    def test_wide_gc_all_fields_shared_children_and_reuse(self):
        source, _ = self.arity_source(512)
        c = source.read_text()
        probe = '''
static void wide_gc_probe(Env e) {
  u64 top = 0;
  for (u64 round = 0; round < 4; ++round) {
    u64 loc = heap_alloc(e, cls_fit(512));
    for (u64 i = 0; i < 512; ++i) {
      u64 child = heap_alloc(e, 1);
      e.mem[child] = JAYDB_NAT_SMALL(i);
      e.mem[child + 1] = jaydb_nat_pow(e, JAYDB_NAT_SMALL(2), JAYDB_NAT_SMALL(96));
      e.mem[loc + i] = term_ctr(CID_Con, child);
    }
    Term value = term_keep(e, term_ctr(CID_Payload, loc), 1);
    term_drop(e, value);
    if (term_peek(e.mem, value) != loc) jaydb_abort(JAYDB_RUNTIME, 111);
    term_drop(e, value);
    if (round && jaydb_heap_next != top) jaydb_abort(JAYDB_RUNTIME, 112);
    top = jaydb_heap_next;
  }
}
'''
        c = c.replace('// Segments\n// ========', probe + '\n// Segments\n// ========')
        c = c.replace('WL_CASE(FID_main)\n', 'WL_CASE(FID_main)\n    wide_gc_probe(e);\n')
        target = self.directory / 'wide-gc.c'
        target.write_text(c)
        BUILD.build_module(target, target.with_suffix('.so'), input_cid='CID_Native_read', output_cid='CID_Native_write')
        module = Module(target.with_suffix('.so'))
        result, output = module.run(b'\x03', memory=4 << 20)
        self.assertEqual((result.status, output), (0, bytes([(512 * 3 + 512 * 511 // 2 + 3) % 256])))
        result, output = module.run_v3(b'\x03', memory=4 << 20)
        self.assertEqual((result.status, output), (0, bytes([(512 * 3 + 512 * 511 // 2 + 3) % 256])))

    def test_address_words_do_not_alias_tags_ids_or_refcounts(self):
        module = self.probe_module('address-words', '''
static void address_words_probe(Env e) {
  const u64 locations[] = { (1ull << 40) - 1, 1ull << 40,
    (1ull << 48) + 7, (1ull << 63) + 9, UINT64_MAX };
  for (u64 i = 0; i < sizeof locations / sizeof *locations; ++i) {
    u64 loc = locations[i], id = 0xFEDCBA9876543210ull;
    Term original = term_ctr(id, loc);
    if (term_aux(original) != id || term_loc(original) != loc
        || term_tag(original) != TAG_CTR || term_rfc(original))
      jaydb_abort(JAYDB_RUNTIME, 121);
    Term shared = rfc_wrap(e, original, 1);
    term_keep(e, shared, 2);
    term_drop(e, shared); // synthetic target is never dereferenced
    if (term_aux(shared) != id || term_peek(e.mem, shared) != loc
        || ((u64)e.mem[term_loc(shared)] & RFC_CNT) != 2)
      jaydb_abort(JAYDB_RUNTIME, 122);
    Term restored = (shared & ~(Term)(RFC_BIT | LOC_MASK)) | term_peek(e.mem, shared);
    if (restored != original) jaydb_abort(JAYDB_RUNTIME, 123);
    heap_free(e, 0, term_loc(shared));
  }
}
''', '    address_words_probe(e);')
        result, output = module.run(b'full address metadata')
        self.assertEqual((result.status, output), (0, b'full address metadata'))

    def test_actual_sparse_arena_allocation_above_offset40(self):
        module = self.probe_module('sparse-offset40', '''
// TEST ONLY: permit a sparse 32-TiB virtual mapping on kernels which reject
// committing it up front. Production mmap flags/policy are unchanged. The
// request still charges the entire real mapped capacity, not resident pages.
#define mmap(A,L,P,F,D,O) mmap(A,L,P,(F)|MAP_NORESERVE,D,O)
static void sparse_offset_probe(Env e) {
  // This really indexes the mapped arena beyond 2^40 slots; no biased base
  // pointer, forged heap size or unmapped-address dereference is used.
  for (u32 i = 0; i < 64; ++i) jaydb_free[i] = 0;
  jaydb_heap_next = (1ull << 40) + 17;
  u64 loc = heap_alloc(e, 1);
  e.mem[loc] = 251;
  e.mem[loc + 1] = term_pak(CID_Nil, 0);
  Term original = term_ctr(CID_Con, loc), shared = term_keep(e, original, 1);
  if (term_loc(original) != loc || term_peek(e.mem, shared) != loc
      || term_loc(shared) <= (1ull << 40)) jaydb_abort(JAYDB_RUNTIME, 124);
  term_drop(e, shared);
  Term fields[2];
  u64 spare = ctr_take(e, shared, 2, fields);
  if (spare != loc || fields[0] != 251 || fields[1] != term_pak(CID_Nil, 0))
    jaydb_abort(JAYDB_RUNTIME, 125);
  spare_free(e, 1, spare);
  if (heap_alloc(e, 1) != loc) jaydb_abort(JAYDB_RUNTIME, 126);
  e.mem[loc] = 1;
  e.mem[loc + 1] = jaydb_nat_pow(e, JAYDB_NAT_SMALL(2), JAYDB_NAT_SMALL(160));
  term_drop(e, term_ctr(CID_Con, loc));
}
''', '    sparse_offset_probe(e);')
        # Existing capacity accounting charges the actual sparse mapping. RSS
        # is not substituted for it. Most pages remain untouched, as in the
        # regular allocator. The old implementation rejected this up front.
        result, output = module.run(b'above offset40', memory=(1 << 45) + (16 << 20))
        self.assertEqual((result.status, output), (0, b'above offset40'))
        self.assertGreater(result.charged_bytes, 1 << 45)
        result, output = module.run(b'again', memory=(1 << 45) + (16 << 20))
        self.assertEqual((result.status, output), (0, b'again'))

    def test_large_arena_is_no_longer_rejected_as_offset_representation(self):
        # With production mmap policy, the host may really refuse this mapping
        # (ENOMEM under vm.overcommit_memory=0). That is SYSTEM, not the former
        # artificial offset40 RUNTIME failure. No OS policy is changed.
        result, output = self.module('echo').run(b'normal mapping', memory=(1 << 45) + (16 << 20))
        self.assertIn(result.status, [0, 5])
        if result.status == 0:
            self.assertEqual(output, b'normal mapping')

    def test_no_allocation_loop_has_deadline(self):
        module = self.probe_module('loop', '', '    for (;;) { __asm__ volatile("" ::: "memory"); }')
        result, _ = module.run(timeout=5_000_000)
        self.assertEqual(result.status, 3)
        self.assertGreaterEqual(result.elapsed_ns, 5_000_000)

    def test_busy_and_abort_do_not_touch_host_input(self):
        module = self.probe_module('busy', '', '    for (;;) { __asm__ volatile("" ::: "memory"); }')
        result_holder = []
        thread = threading.Thread(target=lambda: result_holder.append(module.run(timeout=250_000_000)[0]))
        thread.start()
        time.sleep(0.02)
        published = b'host-published-state'
        before = hashlib.sha256(published).digest()
        result, _ = module.run(published)
        self.assertEqual(result.status, 2)
        thread.join(timeout=2)
        self.assertFalse(thread.is_alive())
        self.assertEqual(result_holder[0].status, 3)
        self.assertEqual(hashlib.sha256(published).digest(), before)

    def test_native_recursion_stops_before_stack_guard(self):
        module = self.probe_module('recursion', '''
__attribute__((noinline)) static u64 recurse(u64 n) {
  volatile u64 value = n;
  return recurse(n + 1) + value;
}
''', '    r0 = recurse(0);')
        result, _ = module.run(timeout=1_000_000_000, stack=512 << 10)
        self.assertEqual(result.status, 4)
        self.assertEqual(result.runtime_code, 0)

    def test_term_stack_stops_at_physical_mapping(self):
        module = self.probe_module('termstack', '', '''
    for (;;) { STK(0) = 0; WL_PUSHN(1); }
''')
        result, _ = module.run(timeout=1_000_000_000, terms=4096)
        self.assertEqual(result.status, 4)

    def test_heap_allocation_exactly_at_capacity_is_permitted(self):
        module = self.probe_module('heap-equal', '', '''
    u64 saved = jaydb_heap_next;
    jaydb_heap_next = jaydb_heap_words - 4;
    u64 exact = heap_alloc(e, 2);
    if (exact + 4 != jaydb_heap_words) jaydb_abort(JAYDB_RUNTIME, 93);
    jaydb_heap_next = saved;
''')
        result, output = module.run(b'equal')
        self.assertEqual((result.status, output), (0, b'equal'))

    def test_compile_stage_deadline(self):
        self.module('echo')
        with self.assertRaises(BUILD.BuildError) as context:
            BUILD.build_module(self.directory / 'echo-generic.c', self.directory / 'expired.so',
                input_cid='CID__________native_effects_read', output_cid='CID__________native_effects_write',
                timeout_seconds=0.000001)
        self.assertEqual(context.exception.category, 'compile_time')

    def test_compiler_huge_exact_budget_has_only_bounded_individual_waits(self):
        import sys
        deadline = BUILD._BUDGET.CompilerDeadline(10 ** 500)
        process = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(0.12); print("complete")'],
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        communicate = process.communicate
        waits = []
        def observed(*args, **kwargs):
            waits.append(kwargs.get('timeout'))
            return communicate(*args, **kwargs)
        process.communicate = observed
        output, error = deadline.wait(process)
        self.assertEqual((process.returncode, output, error), (0, 'complete\n', ''))
        self.assertGreaterEqual(len(waits), 2)
        self.assertTrue(all(0 < wait <= 0.05 for wait in waits))
        self.assertEqual(BUILD._BUDGET.seconds_to_ns('1e500'), 10 ** 509)
        giant = 10 ** 5000
        encoded = BUILD._BUDGET.format_nat(giant)
        self.assertEqual(len(encoded), 5001)
        self.assertEqual(BUILD._BUDGET.parse_nat(encoded), giant)
        self.assertEqual(BUILD._BUDGET.seconds_to_ns(giant), giant * 1_000_000_000)

    def test_compile_huge_decimal_seconds_and_exact_nanoseconds(self):
        self.module('echo')
        source = self.directory / 'echo-generic.c'
        c = source.read_text()
        read = re.search(r'^#define (CID_\w*native_effects_read) \d+$', c, re.M)[1]
        write = re.search(r'^#define (CID_\w*native_effects_write) \d+$', c, re.M)[1]
        report = BUILD.build_module(source, self.directory / 'huge-budget.so', input_cid=read,
                                    output_cid=write, timeout_seconds='1e500', compiler_memory_bytes=10 ** 5000)
        self.assertEqual(int(report['compilerTimeoutNs']), 10 ** 509)
        result, output = Module(self.directory / 'huge-budget.so').run(b'exact huge compiler budget')
        self.assertEqual((result.status, output), (0, b'exact huge compiler budget'))
        with self.assertRaises(BUILD.BuildError) as context:
            BUILD.build_module(source, self.directory / 'ns-expired.so', input_cid=read,
                               output_cid=write, timeout_ns=1)
        self.assertEqual(context.exception.category, 'compile_time')

    def test_compiler_resources_file_exceeds_linux_single_argument_capacity(self):
        import sys
        self.module('echo')
        source = self.directory / 'echo-generic.c'
        c = source.read_text()
        read = re.search(r'^#define (CID_\w*native_effects_read) \d+$', c, re.M)[1]
        write = re.search(r'^#define (CID_\w*native_effects_write) \d+$', c, re.M)[1]
        decimal = '1' + '0' * 140000
        resources = self.directory / 'public-resources.json'
        resources.write_text(json.dumps({'timeout_ns': decimal, 'compiler_memory_bytes': decimal}))
        target = self.directory / 'resources-file.so'
        completed = subprocess.run([sys.executable, str(ROOT / 'tools/native/build.py'), str(source), str(target),
            '--input-cid', read, '--output-cid', write, '--resources-json', str(resources)],
            capture_output=True, text=True, timeout=60)
        self.assertEqual(completed.returncode, 0, completed.stderr or completed.stdout[:1000])
        report = json.loads(completed.stdout)
        self.assertEqual(report['compilerTimeoutNs'], decimal)
        self.assertEqual(report['compilerMemoryBytes'], decimal)
        result, output = Module(target).run(b'limits through private file')
        self.assertEqual((result.status, output), (0, b'limits through private file'))

    def test_v3_absolute_setup_deadline_does_not_restart_at_ffi(self):
        module = self.module('echo')
        report = json.loads((self.directory / 'echo-generic.so.json').read_text())
        self.assertTrue(report['absoluteSetupDeadlineV3'])
        # Deliberately spend the entire original budget before entering C. The
        # legacy duration entry succeeds; the absolute entry must not renew it.
        absolute = time.monotonic_ns() + 5_000_000
        time.sleep(0.010)
        result, output = module.run_v3(b'late', setup=10**500, terms=0, setup_absolute=absolute)
        self.assertEqual((result.status, result.runtime_code, result.stage, output), (3, 0, 0, b''))
        self.assertEqual((result.charged_bytes, result.output_capacity, result.lease), (0, 0, 0))
        result, output = module.run_v3(b'legacy duration', setup=10**500, terms=0)
        self.assertEqual((result.status, output), (0, b'legacy duration'))
        # The new entry uses the absolute epoch alone, even if its ignored
        # request duration is zero or would expire after a single nanosecond.
        for duration in [0, 1]:
            result, output = module.run_v3(b'absolute', setup=duration, terms=0,
                setup_absolute=time.monotonic_ns()+2_000_000_000)
            self.assertEqual((result.status, output), (0, b'absolute'))
        result, output = module.run_v3(setup=0, terms=0, setup_absolute=0)
        self.assertEqual((result.status, result.stage, result.charged_bytes, result.lease), (3, 0, 0, 0))
        result, output = module.run_v3(b'far future', terms=0, setup_absolute=10**500)
        self.assertEqual((result.status, output), (0, b'far future'))

    def test_v3_huge_logical_limits_do_not_reserve_ceiling_bytes(self):
        module = self.module('echo')
        for memory in [1 << 64, 10 ** 5000]:
            result, output = module.run_v3(b'small actual bytes', memory=memory, limit=10 ** 5000,
                setup=10 ** 5000, execution=10 ** 5000, preparation=10 ** 5000)
            self.assertEqual((result.status, result.runtime_code, output), (0, 0, b'small actual bytes'))
            self.assertLess(result.charged_bytes, 3 << 20)
            self.assertEqual(result.output_capacity, 4096)

    def test_v3_empty_output_lease_busy_and_release(self):
        module = self.module('echo')
        result, output = module.run_v3(limit=0, release=False)
        self.assertEqual((result.status, output, result.output, result.output_capacity), (0, b'', None, 0))
        self.assertNotEqual(result.lease, 0)
        self.assertEqual(module.run(b'busy')[0].status, 2)
        self.assertEqual(module.run_v2(b'busy')[0].base.status, 2)
        self.assertEqual(module.run_v3(b'busy')[0].status, 2)
        self.assertEqual(module.library.jaydb_native_release_v3(0), 1)
        self.assertEqual(module.library.jaydb_native_release_v3(result.lease + 1), 1)
        self.assertEqual(module.library.jaydb_native_release_v3(result.lease), 0)
        self.assertEqual(module.library.jaydb_native_release_v3(result.lease), 1)
        for run in (module.run, module.run_v3):
            recovered, output = run(b'after release')
            self.assertEqual((recovered.status, output), (0, b'after release'))

    def test_v3_actual_memory_boundary_and_output_limit_recover(self):
        module = self.module('echo')
        result, _ = module.run_v3(b'x')
        peak = result.charged_bytes
        for memory, expected in [(peak, 0), (peak - 1, 4), (peak, 0)]:
            result, output = module.run_v3(b'x', memory=memory, limit=1)
            self.assertEqual(result.status, expected)
            if expected:
                self.assertEqual((result.lease, result.output, result.output_len, result.output_capacity), (0, None, 0, 0))
            else:
                self.assertEqual(output, b'x')
                self.assertEqual(result.charged_bytes, peak)
        result, _ = module.run_v3(b'xx', limit=1)
        self.assertEqual((result.status, result.lease, result.output), (7, 0, None))
        result, output = module.run_v3(b'xx', limit=2)
        self.assertEqual((result.status, output), (0, b'xx'))

    def test_v3_output_growth_and_stable_nat_pointers(self):
        data = bytes(range(256)) * 280
        result, output = self.module('echo').run_v3(data, setup=10_000_000_000)
        self.assertEqual((result.status, output), (0, data))
        self.assertGreaterEqual(result.output_capacity, len(data))
        self.assertLess(result.output_capacity, 2 * len(data))
        module = self.module('nat_arithmetic')
        a, b = (1 << 4097) + (1 << 2020) + 17, (1 << 2048) + 31
        for op in [0, 2, 5, 15]:
            data = bytes([op]) + str(a).encode() + b'\xff' + str(b).encode()
            expected, reference = module.run(data, timeout=10_000_000_000)
            result, output = module.run_v3(data, setup=10_000_000_000)
            self.assertEqual((expected.status, result.status, output), (0, 0, reference))

    def test_v3_stages_timeouts_epoch_and_huge_durations(self):
        module = self.module('loop_enter')
        before = time.monotonic_ns()
        result, output = module.run_v3(b'\x01\x00\x02', setup=10 ** 500,
            execution=10 ** 500, preparation=10 ** 500)
        after = time.monotonic_ns()
        epoch = result.preparation_started_ns.integer()
        self.assertEqual((result.status, result.stage, output), (0, 2, b'\x02\x01'))
        self.assertLessEqual(before, epoch)
        self.assertLessEqual(epoch, after)
        self.assertEqual(sum(t.integer() for t in result.stage_elapsed_ns), result.elapsed_ns.integer())
        self.assertLessEqual(result.stage_elapsed_ns[2].integer(), after - epoch)
        for options, stage in [({'setup': 1}, 0), ({'execution': 1}, 1), ({'preparation': 1}, 2)]:
            result, _ = module.run_v3(b'\x00', **options)
            self.assertEqual((result.status, result.stage, result.lease), (3, stage, 0))
            if stage == 2:
                self.assertGreater(result.preparation_started_ns.integer(), 0)
        result, output = self.module('loop_nat').run_v3()
        self.assertEqual((result.status, result.stage, output), (0, 2, b'\x01'))

    def test_v3_sparse_word_indices_and_nat_holes_survive_heap_growth(self):
        module = self.probe_module('v3-stable-pages', '''
static void stable_pages_probe(Env e) {
  u64 kept = heap_alloc(e, 0);
  e.mem[kept] = term_pak(CID_Nil, 17);
  Term *pointer = &e.mem[kept];
  const u64 offsets[] = { (1ull << 40) + 511, (1ull << 48) + 511, (1ull << 55) + 511 };
  for (u32 pass = 0; pass < 3; ++pass) {
    jaydb_heap_next = offsets[pass];
    memset(jaydb_free, 0, sizeof jaydb_free);
    Term n = jaydb_nat_new(e, 10000); // header crosses a leaf; local hole survives all growth
    const u64 limbs[] = { 0, 62, 63, 64, 127, 9998, 9999 };
    for (u32 j = 0; j < sizeof limbs / sizeof *limbs; ++j)
      jaydb_nat_put(e, n, limbs[j], (u32)limbs[j] + 11);
    for (u32 j = 0; j < sizeof limbs / sizeof *limbs; ++j)
      if (jaydb_nat_get(e, n, limbs[j]) != limbs[j] + 11) jaydb_abort(JAYDB_RUNTIME, 141);
    if (jaydb_nat_length(e, n) != 10000 || pointer != &e.mem[kept]
        || *pointer != term_pak(CID_Nil, 17)) jaydb_abort(JAYDB_RUNTIME, 142);
    term_drop(e, jaydb_nat_finish(e, n));
    u64 loc = heap_alloc(e, 1);
    e.mem[loc] = 42;
    e.mem[loc + 1] = term_pak(CID_Nil, 0);
    Term shared = term_keep(e, term_ctr(CID_Con, loc), 1);
    term_drop(e, shared);
    Term fields[2];
    u64 spare = ctr_take(e, shared, 2, fields);
    if (loc < offsets[pass] || fields[0] != 42 || fields[1] != term_pak(CID_Nil, 0))
      jaydb_abort(JAYDB_RUNTIME, 143);
    spare_free(e, 1, spare);
  }
}
''', '    stable_pages_probe(e);')
        for _ in range(2):
            result, output = module.run_v3(b'stable high pages', memory=4 << 20)
            self.assertEqual((result.status, result.runtime_code, output), (0, 0, b'stable high pages'))
            self.assertLess(result.charged_bytes, 4 << 20)

    def test_v3_clock_intervals_beyond_u64_and_at_timespec_boundary(self):
        source = self.directory / 'clock-wide.c'
        source.write_text(r'''
#include "guard.h"
#include <time.h>
#include <limits.h>
static jaydb_ns mock_now;
static int invalid_clock;
static struct jaydb_guard guard;
int clock_gettime(clockid_t clock, struct timespec *out) {
  (void)clock;
  out->tv_sec = invalid_clock ? -1 : (time_t)(mock_now / 1000000000u);
  out->tv_nsec = (long)(mock_now % 1000000000u);
  return 0;
}
static unsigned observe(jaydb_ns start, jaydb_ns now, jaydb_ns budget) {
  guard = (struct jaydb_guard){ .wide_time = 1, .stack_high = UINTPTR_MAX,
    .start_wide = start, .stage_started_wide = start, .stage_budget_wide = { budget, budget, budget } };
  mock_now = now;
  jaydb_active = &guard;
  if (!setjmp(guard.escape)) jaydb_poll();
  jaydb_active = NULL;
  return guard.status;
}
int main(void) {
  jaydb_ns word = (jaydb_ns)1 << 64;
  if (observe(word - 100, word + 100, 201) != JAYDB_OK) return 1;
  if (observe(word - 100, word + 100, 200) != JAYDB_TIME) return 2;
  if (observe(1, word + 100, word + 100) != JAYDB_OK) return 3;
  if (observe(1, word + 100, word + 99) != JAYDB_TIME) return 4;
  jaydb_ns last = (jaydb_ns)INT64_MAX * 1000000000u + 999999999u;
  if (observe(0, last, (jaydb_ns)-1) != JAYDB_OK) return 5;
  if (observe(last - 100, last, 101) != JAYDB_OK) return 6;
  if (observe(last - 100, last, 100) != JAYDB_TIME) return 7;
  if (observe(word, word - 1, (jaydb_ns)-1) != JAYDB_SYSTEM) return 8;
  invalid_clock = 1;
  if (observe(0, 1, (jaydb_ns)-1) != JAYDB_SYSTEM) return 9;
  invalid_clock = 0;
  observe(word, word + 100, 100);
  jaydb_active = &guard;
  if (!setjmp(guard.escape)) jaydb_enter_stage(JAYDB_EXECUTION);
  if (guard.status != JAYDB_TIME || guard.stage != JAYDB_SETUP) return 10;
  jaydb_active = NULL;
  return 0;
}
''')
        target = source.with_suffix('')
        compiled = subprocess.run([BUILD.CLANG, '-std=gnu11', '-O2', '-I', str(ROOT / 'native'),
            str(ROOT / 'native/guard.c'), str(source), '-o', str(target)], capture_output=True, text=True)
        self.assertEqual(compiled.returncode, 0, compiled.stderr)
        observed = subprocess.run([str(target)], capture_output=True, text=True, timeout=10)
        self.assertEqual(observed.returncode, 0, observed.stderr)

    def test_v3_abort_immediately_after_mapping_keeps_cleanup_owners(self):
        # Force the real coverage poll immediately after each successful kernel
        # allocation to expire. A mapping must already be charged/reachable.
        header = self.directory / 'allocation-tracker.h'
        header.write_text(r'''
#define _GNU_SOURCE
#include <sys/mman.h>
#include <time.h>
void *tracked_mmap(void *, size_t, int, int, int, off_t);
void *tracked_mremap(void *, size_t, size_t, int, ...);
int tracked_munmap(void *, size_t);
int tracked_clock_gettime(clockid_t, struct timespec *);
#define mmap tracked_mmap
#define mremap tracked_mremap
#define munmap tracked_munmap
#define clock_gettime tracked_clock_gettime
''')
        source = self.directory / 'allocation-owner.c'
        source.write_text(r'''
#include "allocation-tracker.h"
#include "guard.h"
#include <stdlib.h>
#include <string.h>
#undef mmap
#undef mremap
#undef munmap
#undef clock_gettime
#define UNCOVERED __attribute__((no_sanitize("coverage")))
static unsigned acquired, released, expire_after;
static int expired;
UNCOVERED void *tracked_mmap(void *p, size_t n, int prot, int flags, int fd, off_t off) {
  void *mapped = mmap(p, n, prot, flags, fd, off);
  if (mapped != MAP_FAILED && ++acquired == expire_after) expired = 1;
  return mapped;
}
UNCOVERED int tracked_munmap(void *p, size_t n) {
  int status = munmap(p, n);
  if (!status) ++released;
  return status;
}
UNCOVERED void *tracked_mremap(void *p, size_t old, size_t n, int flags, ...) {
  (void)flags;
  // Force a real move while retaining old bytes. This is test instrumentation;
  // production guard.c uses the kernel's ordinary MREMAP_MAYMOVE operation.
  void *mapped = mmap(NULL, n, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (mapped == MAP_FAILED) return mapped;
  memcpy(mapped, p, old);
  if (munmap(p, old)) abort();
  ++released;
  if (++acquired == expire_after) expired = 1;
  return mapped;
}
UNCOVERED int tracked_clock_gettime(clockid_t clock, struct timespec *t) {
  (void)clock;
  *t = (struct timespec){ .tv_sec = expired, .tv_nsec = 100 };
  return 0;
}
#define mmap tracked_mmap
#define mremap tracked_mremap
#define munmap tracked_munmap
typedef uint64_t u64;
typedef uint32_t u32;
typedef unsigned _BitInt(192) Term;
#define FAR static __attribute__((noinline))
#include "arena.inc.c"
FAR void exercise_output(u64 index, uint8_t value) { jaydb_owned_byte(index, value); }
static struct jaydb_guard guard;
UNCOVERED static void reset(void) {
  acquired = released = expired = expire_after = 0;
  guard = (struct jaydb_guard){ .deadline = 1000000000ull,
    .stack_high = UINTPTR_MAX, .memory_limit = 1ull << 30 };
  jaydb_active = &guard;
}
UNCOVERED int main(void) {
  for (unsigned allocation = 1; allocation <= 8; ++allocation) {
    reset();
    expire_after = allocation;
    if (!setjmp(guard.escape)) (void)jaydb_leaf(0, true);
    jaydb_active = NULL;
    jaydb_arena_clear();
    if (guard.status != JAYDB_TIME || acquired != allocation || released != acquired) return 1;
    u64 expected = allocation < 8 ? allocation * 4096ull : 7 * 4096ull + JAYDB_LEAF_BYTES;
    if (guard.memory_peak != expected) return 2;
  }
  reset();
  expire_after = 1;
  if (!setjmp(guard.escape)) exercise_output(0, 7);
  jaydb_active = NULL;
  if (guard.status != JAYDB_TIME || !jaydb_owned_output || jaydb_owned_capacity != 4096
      || guard.memory_peak != 4096) return 3;
  tracked_munmap(jaydb_owned_output, jaydb_owned_capacity);
  jaydb_owned_output = NULL; jaydb_owned_capacity = 0;
  if (acquired != released) return 4;
  reset();
  exercise_output(0, 7);
  uint8_t *before = jaydb_owned_output;
  expire_after = acquired + 1;
  if (!setjmp(guard.escape)) exercise_output(4096, 9);
  jaydb_active = NULL;
  if (guard.status != JAYDB_TIME || jaydb_owned_output == before || !jaydb_owned_output
      || jaydb_owned_capacity != 8192 || guard.memory_peak != 8192 || jaydb_owned_output[0] != 7) return 5;
  tracked_munmap(jaydb_owned_output, jaydb_owned_capacity);
  if (acquired != released) return 6;
  return 0;
}
''')
        arena = self.directory / 'allocation-owner.o'
        guard = self.directory / 'allocation-guard.o'
        target = self.directory / 'allocation-owner'
        common = [BUILD.CLANG, '-std=gnu11', '-O2', '-I', str(ROOT / 'native')]
        commands = [[*common, '-include', str(header), '-c', str(ROOT / 'native/guard.c'), '-o', str(guard)],
            [*common, '-fsanitize-coverage=trace-pc-guard,bb,no-prune', '-c', str(source), '-o', str(arena)],
            [BUILD.CLANG, str(arena), str(guard), '-o', str(target)]]
        for command in commands:
            compiled = subprocess.run(command, capture_output=True, text=True)
            self.assertEqual(compiled.returncode, 0, compiled.stderr)
        observed = subprocess.run([str(target)], capture_output=True, text=True, timeout=10)
        self.assertEqual(observed.returncode, 0, observed.stderr)

    def test_admitted_deep_continuations_use_automatic_term_stack(self):
        target = self.directory / 'admitted-stack.c'
        result = subprocess.run(['node', str(ROOT / 'tests/native/stack_gate.mjs'), str(target)],
            capture_output=True, text=True, timeout=60)
        self.assertEqual(result.returncode, 0, result.stderr[-5000:])
        gate = json.loads(Path(str(target) + '.gate.json').read_text())
        self.assertTrue(gate['primary'] and gate['bendtt'] and gate['sameCheckedBook'])
        report = BUILD.build_module(target, target.with_suffix('.so'),
            input_cid='CID_Native_read', output_cid='CID_Native_write')
        module = Module(target.with_suffix('.so'))
        data = (500001).to_bytes(4, 'little')
        result, _ = module.run_v3(data, memory=64 << 20, terms=8 << 20, setup=20_000_000_000)
        self.assertEqual((result.status, result.runtime_code), (11, 0x5354414b))
        for _ in range(2):
            result, output = module.run_v3(data, memory=64 << 20, terms=0, setup=20_000_000_000)
            self.assertEqual((result.status, result.runtime_code, output), (0, 0, bytes([500001 % 256])))
            self.assertGreater(result.charged_bytes, 8 << 20)
            self.assertLess(result.charged_bytes, 16 << 20)
        self.assertTrue(report['automaticTermStackV3'])
        self.assertTrue(report['nativeStackAudit']['moduleBoundAvailable'])
        self.assertFalse(report['nativeStackAudit']['wholeNativeBoundProved'])
        result, output = module.run_v3((3).to_bytes(4, 'little'), terms=0, memory=2 << 20)
        self.assertEqual((result.status, output), (0, b'\x03'))
        with unlimited_main_stack():
            result, output = module.run_v3(data, memory=64 << 20, terms=0, stack=0, setup=20_000_000_000)
            self.assertEqual((result.status, result.runtime_code, output), (0, 0, bytes([500001 % 256])))
            receipt = {'primary': gate['primary'], 'bendtt': gate['bendtt'],
                'sameCheckedBook': gate['sameCheckedBook'], 'continuations': 500001,
                'automaticTerms': True, 'nativeStackMode': report['automaticNativeStackModeV3'],
                'status': result.status, 'outputHex': output.hex(),
                'localChargedBytes': result.charged_bytes, 'localChargesExcludeOsStack': True,
                'globalAccountingIntegrated': False, 'moduleSha256': report['moduleSha256']}
            (ROOT / 'tests/native/evidence/main-stack-admitted-observed.json').write_text(json.dumps(receipt, indent=2)+'\n')

    def test_book_sized_guard_allows_c_frame_above_65536(self):
        module = self.probe_module('large-frame', r'''
__attribute__((noinline)) static u32 large_frame_probe(void) {
  volatile uint8_t bytes[80000];
  for (u32 i = 0; i < sizeof bytes; ++i) bytes[i] = (uint8_t)i;
  return bytes[12345];
}
''', '    if (large_frame_probe() != 57) jaydb_abort(JAYDB_RUNTIME, 151);')
        report = json.loads((self.directory / 'large-frame.so.json').read_text())
        self.assertGreater(report['maximumCFrameBytes'], 65536)
        self.assertGreater(report['stackGuardReserveBytes'], report['maximumCFrameBytes'])
        for run in (module.run, module.run_v3):
            result, output = run(b'large real C frame')
            self.assertEqual((result.status, output), (0, b'large real C frame'))

    def test_v3_fixed_c_stack_refusal_is_internal_and_callgraph_reports_cycle(self):
        module = self.probe_module('v3-recursion', r'''
__attribute__((noinline)) static u64 recurse(u64 n) {
  volatile u64 value = n;
  return recurse(n + 1) + value;
}
''', '    r0 = recurse(0);')
        result, _ = module.run_v3(stack=512 << 10)
        self.assertEqual((result.status, result.runtime_code), (11, 0x5354414b))
        report = json.loads((self.directory / 'v3-recursion.so.json').read_text())
        self.assertFalse(report['nativeStackAudit']['moduleBoundAvailable'])
        self.assertTrue(report['nativeStackAudit']['stackGrowingCycles'])

    def test_stack_callgraph_distinguishes_musttail_from_recursive_frames(self):
        ir = 'define void @a() {\n  musttail call void @b()\n  ret void\n}\n' + \
             'define void @b() {\n  musttail call void @a()\n  ret void\n}\n'
        audit = BUILD._STACK.analyze(ir, {'a': 80000, 'b': 16}, roots=('a',))
        self.assertTrue(audit['wholeNativeBoundProved'])
        self.assertEqual(audit['moduleBytesExcludingExternal'], 80000)
        recursive = BUILD._STACK.analyze(ir.replace('musttail call void @b()', 'call void @b()'),
                                         {'a': 80000, 'b': 16}, roots=('a',))
        self.assertIsNone(recursive['moduleBytesExcludingExternal'])
        self.assertTrue(recursive['stackGrowingCycles'])
        # Thousands of function nodes do not invoke Python recursion.
        graph = {str(i): {str(i + 1)} for i in range(5000)}
        graph['5000'] = set()
        groups, _ = BUILD._STACK.components(graph)
        self.assertEqual(len(groups), 5001)

    def test_coverage_audit_has_no_python_recursion_depth_quota(self):
        # Entry polls, followed by a large acyclic region. The coverage audit
        # must accept its shape without relying on the Python recursion limit.
        blocks = ''.join(f'b{i}:\n  br label %b{i + 1}\n' for i in range(5000))
        prefix = 'define void @large_cfg() {\n  call void @__sanitizer_cov_trace_pc_guard(ptr null)\n  br label %b0\n'
        ir = prefix + blocks + 'b5000:\n  ret void\n}\n'
        result = BUILD.audit_ir(ir)
        self.assertEqual((result['instrumentedFunctions'], result['basicBlocks']), (1, 5002))
        cyclic = prefix + blocks + 'b5000:\n  br label %b0\n}\n'
        with self.assertRaises(BUILD.BuildError) as context:
            BUILD.audit_ir(cyclic)
        self.assertEqual(context.exception.category, 'coverage')

    def test_compiler_memory_is_logical_and_vm_limit_is_diagnostic_only(self):
        self.module('echo')
        source = self.directory / 'echo-generic.c'
        c = source.read_text()
        read = re.search(r'^#define (CID_\w*native_effects_read) \d+$', c, re.M)[1]
        write = re.search(r'^#define (CID_\w*native_effects_write) \d+$', c, re.M)[1]
        report = BUILD.build_module(source, self.directory / 'logical-memory.so',
            input_cid=read, output_cid=write, compiler_memory_bytes=1)
        self.assertEqual(report['compilerMemoryBytes'], '1')
        self.assertIsNone(report['compilerVmLimitBytes'])
        self.assertFalse(report['compilerPhysicalMemoryEnforcedByBuilder'])
        with self.assertRaises(BUILD.BuildError) as context:
            BUILD.build_module(source, self.directory / 'diagnostic-vm.so', input_cid=read,
                output_cid=write, compiler_memory_bytes=10 ** 500,
                diagnostic_vm_limit_bytes=128 << 20)
        self.assertEqual(context.exception.category, 'compile')

    def test_automatic_term_pages_abort_cleanup_and_stable_bank(self):
        module = self.probe_module('auto-stack-abort', r'''
static bool forced_once;
''', r'''
    if (!forced_once) {
      forced_once = true;
      Term *bank = jaydb_regs;
      Term saved = r0;
      Term *first = jaydb_term_cell(&jaydb_term_stack, 8192);
      *first = term_pak(CID_Nil, 17);
      for (u64 page = 64; page < 128; ++page)
        *jaydb_term_cell(&jaydb_term_stack, page * 512) = page;
      if (bank != jaydb_regs || r0 != saved || *first != term_pak(CID_Nil, 17))
        jaydb_abort(JAYDB_RUNTIME, 152);
      jaydb_active->stage_budget_wide[jaydb_active->stage] = 1;
      jaydb_poll();
    }
''')
        result, _ = module.run_v3(b'private bytes', terms=0)
        self.assertEqual((result.status, result.lease), (3, 0))
        after_abort = result.charged_bytes
        for _ in range(2):
            result, output = module.run_v3(b'recovered', terms=0)
            self.assertEqual((result.status, output), (0, b'recovered'))
            self.assertLess(result.charged_bytes, after_abort)

    def test_cpu1_guard_owner_does_not_poll_or_jump_from_another_host_thread(self):
        module = self.probe_module('guard-owner-concurrent', r'''
static _Atomic unsigned probe_started;
__attribute__((visibility("default"))) unsigned owner_probe_started(void) {
  return atomic_load(&probe_started);
}
''', r'''
    atomic_store(&probe_started, 1);
    for (;;) { __asm__ volatile("" ::: "memory"); }
''')
        entered = module.library.owner_probe_started
        entered.argtypes, entered.restype = [], C.c_uint
        results = []
        thread = threading.Thread(target=lambda: results.append(module.run_v3(setup=300_000_000)))
        thread.start()
        wait_until = time.monotonic() + 2
        while not entered() and time.monotonic() < wait_until:
            time.sleep(0.001)
        self.assertEqual(entered(), 1)
        # Both the instrumented exported probe and run entry execute on this
        # other host thread while the worker's jump target is live.
        result, output = module.run_v3()
        self.assertEqual((result.status, result.lease, output), (2, 0, b''))
        thread.join(2)
        self.assertFalse(thread.is_alive())
        self.assertEqual(results[0][0].status, 3)

    def test_real_llvm_stack_report_keeps_external_f32_obligations(self):
        self.module('f32_read')
        report = json.loads((self.directory / 'f32_read-generic.so.json').read_text())
        audit = report['nativeStackAudit']
        self.assertTrue(audit['moduleBoundAvailable'])
        self.assertFalse(audit['wholeNativeBoundProved'])
        self.assertIn('strtof', audit['externalCallees'])
        self.assertEqual(audit['stackGrowingCycles'], [])
        self.assertEqual(audit['missingFrameMetadata'], [])
        self.assertGreater(audit['musttailEdges'], 0)
        self.assertGreater(report['stackGuardReserveBytes'], report['maximumCFrameBytes'])
        self.assertTrue(report['automaticNativeStackV3'])
        self.assertEqual(report['automaticNativeStackModeV3'], 'linux-main-growdown')

    def test_v3_main_stack_mode_checks_environment_without_changing_limits(self):
        module = self.module('echo')
        previous = resource.getrlimit(resource.RLIMIT_STACK)
        try:
            finite = 8 << 20
            resource.setrlimit(resource.RLIMIT_STACK, (finite, previous[1]))
            result, output = module.run_v3(b'finite OS limit', stack=0, terms=0)
            self.assertEqual((result.status, result.charged_bytes, result.lease, output), (1, 0, 0, b''))
            self.assertEqual(resource.getrlimit(resource.RLIMIT_STACK)[0], finite)
            # Existing relative/absolute explicit-stack paths remain valid.
            result, output = module.run_v3(b'explicit compatibility')
            self.assertEqual((result.status, output), (0, b'explicit compatibility'))
        finally:
            resource.setrlimit(resource.RLIMIT_STACK, previous)
        with unlimited_main_stack():
            results = []
            thread = threading.Thread(target=lambda: results.append(module.run_v3(stack=0, terms=0)))
            thread.start()
            thread.join(2)
            self.assertFalse(thread.is_alive())
            result, output = results[0]
            self.assertEqual((result.status, result.charged_bytes, result.lease, output), (1, 0, 0, b''))
            for absolute in (None, time.monotonic_ns() + 2_000_000_000):
                result, output = module.run_v3(b'main growdown', stack=0, terms=0,
                                               setup_absolute=absolute)
                self.assertEqual((result.status, output), (0, b'main growdown'))

    def test_v3_main_stack_grows_past_explicit_8mib_without_moving_locals(self):
        # Runtime probe, not an admitted Bend program. Every older live array
        # remains readable after actual Linux main-stack VMA growth >8MiB.
        module = self.probe_module('main-stack-growth', r'''
static uintptr_t lowest_probe_address;
static long probe_tid;
__attribute__((visibility("default"))) uintptr_t main_probe_lowest(void) {
  return lowest_probe_address;
}
__attribute__((visibility("default"))) long main_probe_tid(void) { return probe_tid; }
__attribute__((noinline)) static u64 main_stack_recurse(u64 depth) {
  volatile uint8_t bytes[1 << 20];
  for (u64 at=0; at<sizeof bytes; at+=4096) bytes[at]=(uint8_t)(depth+at/4096);
  bytes[sizeof bytes-1]=(uint8_t)(depth^23);
  lowest_probe_address=(uintptr_t)bytes;
  u64 child=depth ? main_stack_recurse(depth-1) : 0;
  for (u64 at=0; at<sizeof bytes; at+=4096)
    if (bytes[at]!=(uint8_t)(depth+at/4096)) jaydb_abort(JAYDB_RUNTIME,171);
  return child+bytes[0]+bytes[sizeof bytes-1];
}
''', r'''
    __asm__ volatile("syscall" : "=a"(probe_tid) : "a"(186) : "rcx","r11","memory");
    if (main_stack_recurse(9)!=262) jaydb_abort(JAYDB_RUNTIME,172);
''')
        report = json.loads((self.directory / 'main-stack-growth.so.json').read_text())
        self.assertGreater(report['maximumCFrameBytes'], 1 << 20)
        self.assertFalse(report['nativeStackAudit']['moduleBoundAvailable'])
        machine = subprocess.run(['objdump', '-d', '--disassemble=main_stack_recurse',
            str(self.directory / 'main-stack-growth.so')], check=True, capture_output=True, text=True).stdout
        self.assertRegex(machine, r'sub\s+\$0x1000,%rsp')
        self.assertRegex(machine, r'(?:mov|or)q?\s+\$0x0,\(%rsp\)')
        result, _ = module.run_v3(b'fixed refuses', stack=8 << 20, terms=0, memory=64 << 20)
        self.assertEqual((result.status, result.runtime_code), (11, 0x5354414b))
        fixed_code = result.runtime_code
        def stack_interval():
            line = next(line for line in Path('/proc/self/maps').read_text().splitlines() if line.endswith('[stack]'))
            return tuple(int(part,16) for part in line.split()[0].split('-'))
        with unlimited_main_stack():
            before = stack_interval()
            for _ in range(2):
                result, output = module.run_v3(b'grown locals intact', stack=0, terms=0, memory=64 << 20)
                self.assertEqual((result.status, result.runtime_code, output), (0, 0, b'grown locals intact'))
                self.assertLess(result.charged_bytes, 8 << 20)  # local charges exclude the OS stack
            after = stack_interval()
            low = module.library.main_probe_lowest
            low.restype = C.c_uint64
            self.assertLessEqual(after[0], low())
            self.assertLess(low(), after[1])
            self.assertGreater(after[1]-after[0], 10 << 20)
            tid = module.library.main_probe_tid
            tid.restype = C.c_long
            self.assertEqual(tid(), os.getpid())
            self.assertGreaterEqual(before[0], after[0])
            receipt = {'probeIsAdmittedClient': False, 'fixed8MiBStatus': 11, 'fixed8MiBCode': fixed_code,
                'mainModeStatus': result.status, 'outputHex': output.hex(),
                'stackBytesBefore': before[1]-before[0], 'stackBytesAfter': after[1]-after[0],
                'mainTidMatchesPid': tid()==os.getpid(), 'localsStayedValid': True,
                'pageProbesVerifiedInMachineCode': True, 'maximumCFrameBytes': report['maximumCFrameBytes'],
                'localChargesExcludeOsStack': True, 'moduleSha256': report['moduleSha256']}
            (ROOT / 'tests/native/evidence/main-stack-growth-observed.json').write_text(json.dumps(receipt,indent=2)+'\n')

    def test_v3_main_stack_owner_rejects_concurrent_call_without_cross_thread_longjmp(self):
        module = self.probe_module('main-stack-concurrent', r'''
static _Atomic unsigned main_probe_started;
__attribute__((visibility("default"))) unsigned main_owner_started(void) {
  return atomic_load(&main_probe_started);
}
''', r'''
    atomic_store(&main_probe_started,1);
    for (;;) { __asm__ volatile("" ::: "memory"); }
''')
        started = module.library.main_owner_started
        started.argtypes, started.restype = [], C.c_uint
        results = []
        def other_thread():
            until = time.monotonic()+2
            while not started() and time.monotonic()<until:
                time.sleep(0.001)
            results.append(module.run_v3())
        with unlimited_main_stack():
            thread = threading.Thread(target=other_thread)
            thread.start()
            result, output = module.run_v3(stack=0, terms=0, setup=300_000_000)
            thread.join(2)
            self.assertFalse(thread.is_alive())
            self.assertEqual((result.status, result.lease, output), (3, 0, b''))
            self.assertEqual((results[0][0].status, results[0][0].lease), (2, 0))

    def test_v3_main_stack_preserves_deadline_longjmp_cleanup_and_f32(self):
        echo = self.module('echo')
        alternating = self.probe_module('main-stack-alternating',
            'static unsigned main_stack_calls;', r'''
    jaydb_enter_stage(JAYDB_EXECUTION);
    if (++main_stack_calls & 1) for (;;) { __asm__ volatile("" ::: "memory"); }
''')
        with unlimited_main_stack():
            result, _ = echo.run_v3(stack=0, terms=0, setup=0, setup_absolute=1)
            self.assertEqual((result.status, result.stage, result.charged_bytes, result.lease), (3, 0, 0, 0))
            for _ in range(2):
                result, _ = alternating.run_v3(stack=0, terms=0, execution=5_000_000)
                self.assertEqual((result.status, result.stage, result.lease), (3, 1, 0))
                result, output = alternating.run_v3(b'after main longjmp', stack=0, terms=0)
                self.assertEqual((result.status, output), (0, b'after main longjmp'))
            for fixture, data in [('f32_read', b'1.25'), ('f32_read', b'9'*10000), ('f32_show', b'')]:
                module = self.module(fixture)
                old, expected = module.run_v3(data, terms=0)
                new, actual = module.run_v3(data, terms=0, stack=0)
                self.assertEqual((old.status, new.status, actual), (0, 0, expected))

    def test_nat48_classification(self):
        result, _ = self.module('nat48', 'official').run()
        self.assertEqual((result.status, result.runtime_code), (8, 5))
        result, output = self.module('nat48').run()
        self.assertEqual((result.status, result.runtime_code, output), (0, 0, b'\x00'))

    def test_work_deadline(self):
        result, _ = self.module('work').run(timeout=5_000_000)
        self.assertEqual(result.status, 3)
        self.assertGreaterEqual(result.elapsed_ns, 5_000_000)

    def test_separate_modules(self):
        echo, array = self.module('echo'), self.module('array32')
        for _ in range(3):
            self.assertEqual(echo.run(b'abc')[1], b'abc')
            self.assertEqual(array.run()[1], b'\x20')

    def test_reject_uninstrumented_cycle(self):
        ir = '''define void @bad() {
  call void @__sanitizer_cov_trace_pc_guard(ptr null)
  br label %loop
loop:
  br label %loop
}
'''
        with self.assertRaises(BUILD.BuildError) as context:
            BUILD.audit_ir(ir)
        self.assertEqual(context.exception.category, 'coverage')

    def test_reject_uninstrumented_recursion(self):
        with self.assertRaises(BUILD.BuildError):
            BUILD.audit_ir('define void @bad() {\n  call void @bad()\n  ret void\n}\n')


if __name__ == '__main__':
    unittest.main(verbosity=2)
