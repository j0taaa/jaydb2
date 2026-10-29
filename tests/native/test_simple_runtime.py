"""Generate three primary-checked Books; verify their native representation/ABI.

These interoperability checks do not claim a proof of C compilation.
"""
from __future__ import annotations
import ctypes as C
import json
from pathlib import Path
import re
import struct
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.native import build_simple as BUILD
from tools.service.abi_simple import SimpleModule, Request, Result, NativeFailure
from tools.service.entry import prepare_entry

BEND = ROOT/'.tools/bend-source-2.0.39/bend2'


class RuntimeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        prepare_entry()
        cls.temporary = tempfile.TemporaryDirectory(prefix='jaydb-runtime-test-')
        cls.directory = Path(cls.temporary.name)
        cls.paths, cls.reports = {}, {}

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    @classmethod
    def compile(cls, name):
        if name in cls.paths:
            return cls.paths[name]
        source, output = cls.directory/(name+'.c'), cls.directory/(name+'.so')
        run = subprocess.run(['node', str(ROOT/'tests/native/emit_fixture.mjs'),
            str(BEND), str(ROOT/'tests/native/fixtures'/(name+'.bend')), str(source)],
            capture_output=True, text=True, timeout=60)
        if run.returncode:
            raise AssertionError(run.stdout+run.stderr)
        code = source.read_text()
        def cid(stem, required=False):
            match = re.search(r'^#define (CID_(?:\w*_)?'+stem+r') \d+$', code, re.M)
            if required and not match:
                raise AssertionError('Missing native binding: '+stem)
            return match[1] if match else None
        bindings = dict(input_cid=cid('(?:native_effects_)?read'),
                        output_cid=cid('(?:native_effects_)?write'))
        if name == 'loop':
            for key, stem in [('loop','loop'),('continue','Continuar'),('finish','Encerrar'),
                              ('inconsistent','Inconsistente'),('prepare','Preparar')]:
                bindings[key+'_cid'] = cid('native_effects_'+stem, required=True)
        cls.reports[name] = BUILD.build_module(source, output, **bindings)
        cls.paths[name] = output
        return output

    def module(self, name):
        module = SimpleModule(self.compile(name))
        self.addCleanup(module.close)
        return module

    def test_binary_effects_capacity_and_recovery(self):
        # All octet values, NUL and empty bytes survive the effect/ABI boundary.
        module = self.module('echo')
        for data in (bytes(range(256)), b'', b'\0\xffagain'):
            self.assertEqual(module.run(data, capacity=len(data)), data)
        with self.assertRaises(NativeFailure) as failure:
            module.run(b'abc', capacity=2)
        self.assertEqual((failure.exception.status, failure.exception.fatal), (7, False))
        self.assertEqual(module.run(b'abc', capacity=3), b'abc')
        module.close()
        with self.assertRaises(RuntimeError):
            module.run(b'x', capacity=1)

    def test_generic_representations_and_captured_function(self):
        # A runtime limb value, captured function, Array and F32 constructors
        # cross C's generic Term representation without archived C fixtures.
        module = self.module('representation')
        self.assertEqual(module.run(b'\0\x11', capacity=64),
            str(680564733841876926926749214863536422913+17).encode())
        self.assertEqual(module.run(b'\1', capacity=1), b'\x20')
        self.assertEqual(module.run(b'\2' + b'1.25', capacity=5), b'\1'+struct.pack('<f', 1.25))
        self.assertEqual(module.run(b'\2' + b'1\0garbage', capacity=5), b'\0')

    def test_native_loop_prepare_and_continue(self):
        # Prepare resumes through native protocol control and preserves state.
        self.assertEqual(self.module('loop').run(b'\1\0\2', capacity=2), b'\2\1')

    def test_abi_output_ownership_and_loaded_identity(self):
        # The six-word Result has one live output owner until explicit release.
        path = self.compile('echo')
        module = self.module('echo')
        self.assertEqual((C.sizeof(Request), C.sizeof(Result)), (32, 48))
        report = self.reports['echo']
        self.assertEqual(set(report['exportedSymbols']), {
            'jaydb_native_run_v6', 'jaydb_native_describe_v6', 'jaydb_native_release_v6'})
        source = (C.c_uint8*1)(65)
        request, result = Request(6, 32, source, 1, 1), Result()
        self.assertEqual(module._run(C.byref(request), C.byref(result)), 0)
        self.assertTrue(result.lease)
        try:
            self.assertEqual(C.string_at(result.output, result.output_len), b'A')
            rejected = Result()
            self.assertEqual(module._run(C.byref(request), C.byref(rejected)), 2)
        finally:
            self.assertEqual(module._release(result.lease), 0)
        self.assertEqual(module.run(b'B', capacity=1), b'B')
        target = self.directory/'wrong-identity.so'
        target.write_bytes(path.read_bytes())
        target.with_suffix('.so.json').write_text(json.dumps(dict(report, buildIdentitySha256='0'*64)))
        with self.assertRaisesRegex(RuntimeError, 'descriptor/identity'):
            SimpleModule(target)


if __name__ == '__main__':
    unittest.main(verbosity=2)
