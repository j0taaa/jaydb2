"""ABI6 native integration: positive fixtures are primary-checked test Books.

The archived Codec C additionally carries its original both-checker/same-Book
record. These runtime tests do not claim the full revised database contract.
They never update historical evidence or execute the physical-budget suite.
"""
from __future__ import annotations
import ctypes as C
import hashlib
import json
import os
from pathlib import Path
import random
import re
import resource
import shutil
import struct
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.native import build_simple as BUILD
from tools.service import build_loading, build_lifecycle
from tools.service.loading import Runtime, LibraryScope
from tools.service.lifecycle import LifecycleRuntime, OutputLease
from tools.service.abi_simple import (SimpleModule, Request, Result, NativeFailure,
    NativeOwnershipPending)

BEND = ROOT/'.tools/bend-source-2.0.39/bend2'


class SimpleRuntimeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.previous_stack = resource.getrlimit(resource.RLIMIT_STACK)
        if cls.previous_stack[1] != resource.RLIM_INFINITY:
            raise RuntimeError('The native main-stack profile needs unlimited hard stack')
        resource.setrlimit(resource.RLIMIT_STACK, (resource.RLIM_INFINITY, cls.previous_stack[1]))
        cls.temporary = tempfile.TemporaryDirectory(prefix='jaydb-simple-tests-')
        cls.directory = Path(cls.temporary.name)
        # Freeze the independent native fixture sources before parallel contract work.
        fixtures = cls.directory/'fixtures'
        fixtures.mkdir()
        for source in (ROOT/'tests/native/fixtures').glob('*.bend'):
            (fixtures/source.name).write_text(source.read_text().replace(
                '../../../native/effects.bend', str(ROOT/'native/effects.bend')))
        # Generic Array.new constructs all leaves. Depth eight exercises it
        # without requesting the 2**32 leaves of the old refusal diagnostic.
        (fixtures/'array_new8.bend').write_text((fixtures/'array_new32.bend').read_text()
            .replace('Array.new(U32, 32n, 7)', 'Array.new(U32, 8n, 7)'))
        cls.fixtures = fixtures
        cls.paths, cls.reports, cls.sources = {}, {}, {}
        build_loading.build(cls.directory/'loading.so')
        build_lifecycle.build(cls.directory/'lifecycle.so')
        cls.loading = Runtime.load(cls.directory/'loading.so')
        cls.lifecycle = LifecycleRuntime.load(cls.directory/'lifecycle.so', loading_runtime=cls.loading)

    @classmethod
    def tearDownClass(cls):
        if cls.lifecycle.live_leases:
            raise AssertionError('Native output leases survived the tests')
        destination = os.environ.get('JAYDB_SIMPLE_EVIDENCE_DIR')
        if destination:
            destination = Path(destination)
            destination.mkdir(parents=True, exist_ok=False)  # never overwrite a prior run
            shutil.copytree(cls.fixtures, destination/'primary-fixtures')
            for name, binary in cls.paths.items():
                for file in (binary, binary.with_suffix('.c'), binary.with_suffix('.so.json')):
                    shutil.copy2(file, destination/file.name)
                prepared, _ = BUILD.prepare_source(cls.sources[name], **cls.reports[name]['bindings'])
                assert hashlib.sha256(prepared.encode()).hexdigest() == cls.reports[name]['preparedSourceSha256']
                (destination/(name+'.prepared.c')).write_text(prepared)
            identities = [ROOT/'tools/native/generic.mjs', ROOT/'tests/native/emit_fixture.mjs',
                ROOT/'native/effects.bend', ROOT/'native/effects.c', BEND/'base.bend',
                BEND/'bend.ts', BEND/'comp.ts', ROOT/'tests/native/test_simple_runtime.py']
            record = dict(abiVersion=6, fullRevisedContractProved=False,
                positiveFixtureScope='Primary checker and same in-memory Book emission; not production admission',
                archivedFixtureScope='Original Codec and closure arity2048 use prior primary+bendtt+sameCheckedBook records',
                originalEvidenceUntouched=True, liveOutputLeasesAfterTests=len(cls.lifecycle.live_leases),
                inputIdentities={str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                    for path in identities}, modules=cls.reports)
            (destination/'artifacts.json').write_text(json.dumps(record, indent=2)+'\n')
        resource.setrlimit(resource.RLIMIT_STACK, cls.previous_stack)
        cls.temporary.cleanup()

    @classmethod
    def compile(cls, name):
        if name in cls.paths:
            return cls.paths[name]
        target = cls.directory/name
        if name in ('original-codec', 'wide-captured-closure'):
            stem = 'field-codec' if name == 'original-codec' else 'stack-arity2048'
            source = ROOT/'tests/native/evidence'/(stem+'.c')
            suffix = '.c.constructors.json' if name == 'original-codec' else '.c.gate.json'
            checked = json.loads(source.with_suffix(suffix).read_text())
            assert all(checked[key] for key in ('primary', 'bendtt', 'sameCheckedBook'))
            if name == 'original-codec':
                assert all(checked[key] for key in ('inspectionUsedSameBookObject',
                    'checkedBookFrozenBeforeInspection', 'emittedCUnchanged'))
            assert hashlib.sha256(source.read_bytes()).hexdigest() == checked['cSha256']
            # A private copy keeps all archived evidence byte-for-byte untouched.
            target.with_suffix('.c').write_bytes(source.read_bytes())
        else:
            completed = subprocess.run(['node', str(ROOT/'tests/native/emit_fixture.mjs'),
                str(BEND), str(cls.fixtures/(name+'.bend')), str(target.with_suffix('.c')), 'generic'],
                capture_output=True, text=True)
            if completed.returncode:
                raise AssertionError(completed.stdout+completed.stderr)
        source = target.with_suffix('.c').read_text()
        def cid(stem, required=False):
            match = re.search(r'^#define (CID_(?:\w*_)?'+stem+r') \d+$', source, re.M)
            if required and not match:
                raise AssertionError('Missing test binding: '+stem)
            return match[1] if match else None
        options = dict(input_cid=cid('(?:native_effects_)?read'),
                       output_cid=cid('(?:native_effects_)?write'))
        if name.startswith('loop'):
            for key, stem in [('loop', 'loop'), ('continue', 'Continuar'), ('finish', 'Encerrar'),
                              ('inconsistent', 'Inconsistente'), ('prepare', 'Preparar')]:
                options[key+'_cid'] = cid('native_effects_'+stem, required=True)
            options['enter_cid'] = cid('native_effects_enter')
        cls.reports[name] = BUILD.build_module(target.with_suffix('.c'), target.with_suffix('.so'), **options)
        cls.sources[name] = source
        cls.paths[name] = target.with_suffix('.so')
        return cls.paths[name]

    def module(self, name):
        module = SimpleModule(self.compile(name), loading_runtime=self.loading, lifecycle_runtime=self.lifecycle)
        self.addCleanup(module.close)
        return module

    def test_binary_all_bytes_non_nul_and_repeat(self):
        module = self.module('echo')
        tasks = sorted(os.listdir('/proc/self/task'))
        children = Path('/proc/self/task/'+str(os.getpid())+'/children').read_text()
        tracer = re.search(r'^TracerPid:\s*(\d+)', Path('/proc/self/status').read_text(), re.M)[1]
        self.assertEqual(tracer, '0')
        for data in [bytes(range(256)), bytes(range(1, 256)), b'\0\xff\xc0\x80', b'',
                     bytes(range(256))*256] + [b'repeat']*20:
            self.assertEqual(module.run(data, capacity=len(data)), data)
            self.assertEqual(self.lifecycle.live_leases, ())
        self.assertEqual(sorted(os.listdir('/proc/self/task')), tasks)
        self.assertEqual(Path('/proc/self/task/'+str(os.getpid())+'/children').read_text(), children)

    def test_logical_capacity_equality_failure_and_recovery(self):
        module = self.module('echo')
        self.assertEqual(module.run(b'abc', capacity=3), b'abc')
        with self.assertRaises(NativeFailure) as context:
            module.run(b'abc', capacity=2)
        self.assertEqual(context.exception.status, 7)
        self.assertFalse(context.exception.fatal)
        self.assertFalse(context.exception.infrastructure)
        self.assertEqual(module.run(b'', capacity=0), b'')
        self.assertEqual(module.run(b'x', capacity=10**100), b'x')
        self.assertEqual(self.lifecycle.live_leases, ())

    def test_general_recursion_and_continuation_stack(self):
        module = self.module('stack_depth')
        for depth in (0, 1, 4097, 40000):
            self.assertEqual(module.run(depth.to_bytes(4, 'little'), capacity=1), bytes([depth & 255]))

    def test_arbitrary_nat_capturing_closures_and_arithmetic(self):
        module = self.module('nat_arithmetic')
        randomizer = random.Random(6123)
        pairs = [((1<<48)+1, (1<<161)+9), ((1<<256)-1, (1<<129)+17)]
        pairs += [(randomizer.getrandbits(220), randomizer.getrandbits(150)) for _ in range(4)]
        for a, b in pairs:
            for operation, answer in ((0, a+b), (1, max(0, a-b)), (2, a*b),
                                      (3, a//b), (4, a%b), (15, a+b)):
                data = bytes([operation])+str(a).encode()+b'\xff'+str(b).encode()
                self.assertEqual(module.run(data, capacity=1024), str(answer).encode())

    def test_generic_array_representations(self):
        for name, expected in (('array32', b'\x20'), ('array_new8', b'\x07')):
            self.assertEqual(self.module(name).run(b'', capacity=1), expected)

    def test_wide_captured_closure_from_same_checked_book(self):
        module = self.module('wide-captured-closure')
        for value in (0, 1, 127, 255):
            expected = (2048*value + 2048*2047//2 + 3) % 256
            self.assertEqual(module.run(bytes([value]), capacity=1), bytes([expected]))

    def test_f32_binary_strings_and_rounding(self):
        module = self.module('f32_read')
        for token in (b'1.25', b'-0', b'16777217', b'1e-44', b'0.1234567890123456789'):
            self.assertEqual(module.run(token, capacity=5), b'\1'+struct.pack('<f', float(token)))
        for token in (b'1\0garbage', b'\0', b'no', b'1 '):
            self.assertEqual(module.run(token, capacity=5), b'\0')
        self.assertEqual(module.run(b'1.'+b'0'*50000+b'1', capacity=5), b'\1'+struct.pack('<f', 1.0))
        self.assertEqual(self.module('f32_unicode').run(b'1\0x', capacity=9), bytes(9))

    def test_loop_and_prepare_are_native_protocol_control(self):
        for name in ('loop', 'loop_enter'):
            self.assertEqual(self.module(name).run(b'\x01\0\x02', capacity=2), b'\x02\x01')
        self.assertEqual(self.module('loop_nat').run(b'', capacity=1), b'\1')

    def test_original_codec_general_segments(self):
        module = self.module('original-codec')
        wires = [b'\0', b'\1', b'\2', b'\3'+bytes(range(8)),
            b'\4'+(3).to_bytes(8, 'big')+b'abc',
            b'\5'+(3).to_bytes(8, 'big')+b'\0\1\2']
        for wire in wires:
            self.assertEqual(module.run(wire, capacity=1024), wire)
        for invalid in (b'', b'\7', b'\4'+(5).to_bytes(8, 'big')+b'ab', b'\0\0'):
            self.assertEqual(module.run(invalid, capacity=1), b'\xfe')

    def test_leases_hold_output_busy_and_durable_release(self):
        module = self.module('echo')
        for data in (b'lease\0\xff', b''):
            source = (C.c_uint8*max(1, len(data))).from_buffer_copy(data or b'\0')
            request = Request(6, 32, source, len(data), len(data))
            result = Result()
            owner = OutputLease.prepare(self.lifecycle, module._library_owner, result,
                                        result_owner=(source, request, result))
            self.assertEqual(owner.invoke(module._run, C.byref(request), C.byref(result)), 0)
            self.assertTrue(result.lease)
            self.assertFalse(any(result.compatibility_reserved))
            rejected = Result()
            self.assertEqual(module._run(C.byref(request), C.byref(rejected)), 2)
            self.assertEqual(C.string_at(result.output, result.output_len), data)
            owner.release()
            owner.release()  # durable receipt prevents a second release call
            self.assertTrue(owner.resolved)
            self.assertEqual(module.library.jaydb_native_release_v3(result.lease), 1)

    def test_exceptions_release_and_pending_lease_blocks_dlclose(self):
        module = self.module('echo')
        original = OutputLease.invoke
        def interrupted(owner, *arguments):
            original(owner, *arguments)
            raise RuntimeError('interrupted after native returned')
        with patch.object(OutputLease, 'invoke', interrupted):
            with self.assertRaisesRegex(RuntimeError, 'interrupted after'):
                module.run(b'receipt', capacity=7)
        self.assertEqual(self.lifecycle.live_leases, ())
        with patch.object(LifecycleRuntime, 'release_v3', side_effect=RuntimeError('release temporarily unavailable')):
            with self.assertRaises(NativeOwnershipPending):
                module.run(b'retained', capacity=8)
            with self.assertRaises(NativeOwnershipPending):
                module.close()
            self.assertFalse(module._library_owner.close_receipt.entered)
            self.assertTrue(self.lifecycle.has_live_leases(module._library_owner))
        module.close()
        self.assertTrue(module._library_owner.closed)

    def test_manifest_loaded_identity_and_active_code_has_no_observer(self):
        path = self.compile('echo')
        report = self.reports['echo']
        self.assertEqual((report['abiVersion'], report['requestBytes'], report['resultBytes']), (6, 32, 136))
        self.assertFalse(report['semanticCorrespondenceProved'])
        self.assertEqual(set(report['exportedSymbols']), {'jaydb_native_run_v6',
            'jaydb_native_describe_v6', 'jaydb_native_release_v3'})
        prepared, _ = BUILD.prepare_source(self.sources['echo'], **report['bindings'])
        self.assertNotRegex(prepared, r'\b(?:jaydb_poll|clock_gettime|ptrace|jaydb_codec_accounted)\s*\(')
        imports = subprocess.run(['/usr/bin/nm', '-D', str(path)], check=True,
            capture_output=True, text=True).stdout
        self.assertNotRegex(imports, r'\b(?:clock_gettime|ptrace|pthread_create|timer_create|__sanitizer_cov_\w+)\b')
        target = self.directory/'bad-loaded-id.so'
        target.write_bytes(path.read_bytes())
        altered = dict(report, buildIdentitySha256='0'*64)
        target.with_suffix('.so.json').write_text(json.dumps(altered))
        scope = LibraryScope()
        with self.assertRaisesRegex(RuntimeError, 'descriptor/identity'):
            SimpleModule(target, self.loading, self.lifecycle, scope)
        self.assertEqual(scope.live_owners, ())

    def test_actual_mapping_failure_is_infrastructure_and_poisoned(self):
        path = self.compile('echo')
        script = '''
import ctypes as C, resource, sys
from tools.service.abi_simple import Request,Result
resource.setrlimit(resource.RLIMIT_STACK,(resource.RLIM_INFINITY,resource.RLIM_INFINITY))
library=C.CDLL(sys.argv[1]); function=library.jaydb_native_run_v6
function.argtypes=[C.POINTER(Request),C.POINTER(Result)]; function.restype=C.c_uint32
source=(C.c_uint8*1)(1); request=Request(6,32,source,1,1); result=Result()
q,r=C.byref(request),C.byref(result)
previous=resource.getrlimit(resource.RLIMIT_AS)
try:
 resource.setrlimit(resource.RLIMIT_AS,(0,previous[1]))
 status=function(q,r)
finally:
 resource.setrlimit(resource.RLIMIT_AS,previous)
assert status==result.status==5 and result.runtime_code==12,(status,result.status,result.runtime_code)
assert not result.lease and not result.output and not result.output_len
assert function(q,r)==5 and not result.lease
print('real-mmap-ENOMEM; instance-poisoned; no-output-lease')
'''
        completed = subprocess.run([sys.executable, '-c', script, str(path)], cwd=ROOT,
            capture_output=True, text=True)
        self.assertEqual(completed.returncode, 0, completed.stdout+completed.stderr)
        self.assertIn('real-mmap-ENOMEM', completed.stdout)


if __name__ == '__main__':
    program = unittest.main(verbosity=2, exit=False)
    destination = os.environ.get('JAYDB_SIMPLE_EVIDENCE_DIR')
    if destination and Path(destination).is_dir():
        result = program.result
        record = dict(success=result.wasSuccessful(), testsRun=result.testsRun,
            failures=len(result.failures), errors=len(result.errors), skipped=len(result.skipped))
        with (Path(destination)/'result.json').open('x') as output:
            output.write(json.dumps(record, indent=2)+'\n')
    raise SystemExit(0 if program.result.wasSuccessful() else 1)
