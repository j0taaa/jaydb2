"""Opt-in tests on a real NVIDIA GPU; no skip or synthetic GPU results.
Run under the experiment heavy lock. CPU default regressions live separately.
"""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from tests.service.test_end_to_end import ROOT, Server

CODE = (ROOT/'experiments/gpu/Client.bend').read_text()
PROOF = (ROOT/'experiments/gpu/ClientProof.bend').read_text()
CONCRETE = (ROOT/'examples/access/ClientProof.bend').read_text()


def oracle(depth):
    total = 0
    for seed in range(1 << depth):
        x = seed
        for _ in range(64):
            x = ((x ^ (x >> 16))*1664525 + 1013904223) & 0xffffffff
        total = (total + x) & 0xffffffff
    return total


class GpuTests(unittest.TestCase):
    def server(self, gpu=True, env=None):
        server = Server(ROOT/'examples/access', env=env,
                        options=['--threads', '1', '--gpu', '512' if gpu else 'off'])
        self.addCleanup(server.close)
        return server

    def register(self, server, code=CODE):
        response = server.prepared(0, code, 'alice-token', proof=PROOF)
        self.assertEqual(response['status'], 'prepared', server.diagnostics())
        return response['value']

    def execute(self, server, handle, credential, replacement):
        result = server.prepared(1, handle, credential, replacement)
        self.assertEqual(result, {'status': 'success', 'value': oracle(len(replacement))}, server.diagnostics())

    def test_unwrapped_cpu_and_gpu_results_publication_authentication_and_refusal(self):
        # Both paths compile the same literal C, and consume fresh runtime args.
        for gpu in [False, True]:
            with self.subTest(gpu=gpu):
                server = self.server(gpu, env=dict(os.environ, BENDRTS='--gpu-build'))
                small = 's'
                self.assertEqual(server.call(CODE, CONCRETE, 'alice-token', small),
                    {'status': 'success', 'value': oracle(len(small))}, server.diagnostics())
                self.assertEqual(server.call(CODE, CONCRETE, 'alice-token', 'old'),
                    {'status': 'authentication', 'value': None})
                receipt = server.prepared(0, CODE, small, proof=PROOF)
                self.assertEqual(receipt['status'], 'prepared', server.diagnostics())
                handle = receipt['value']
                self.execute(server, handle, small, 'large-runtime!') # runtime depth 14
                credential = 'large-runtime!'
                self.assertEqual(len(credential), 14)
                self.assertEqual(server.prepared(1, handle, credential),
                    {'status': 'refusal', 'value': 'cancelled'}, server.diagnostics())
                self.assertEqual(server.call(CODE, CONCRETE, credential),
                    {'status': 'refusal', 'value': 'cancelled'}, server.diagnostics())
                self.execute(server, handle, credential, 'x')
                self.assertEqual(server.prepared(1, handle, credential, 'stale'),
                    {'status': 'authentication', 'value': None})
                forbidden = CODE.replace('D.ReadCell{D.Users{}, id,', 'D.ReadCell{D.Users{}, "bob",')
                self.assertEqual(server.prepared(0, forbidden, 'x', proof=PROOF),
                    {'status': 'certificate', 'value': None}, server.diagnostics())
                self.assertIn('PRIMARY_CHECK', server.diagnostics())
                self.assertEqual(server.prepared(2, handle, 'x'), {'status': 'invalidated', 'value': None})
                self.assertEqual(server.prepared(1, handle, 'x'), {'status': 'failure', 'value': None})
                server.finish()

    def test_bundle_integrity_real_launches_and_failure_rollback(self):
        with tempfile.TemporaryDirectory(prefix='gpu-faults-') as tmp:
            folder = Path(tmp)
            library, fault, trace = folder/'faults.so', folder/'fault', folder/'trace'
            subprocess.run(['gcc', '-shared', '-fPIC', str(ROOT/'tests/service/gpu_faults.c'),
                            '-o', str(library), '-ldl'], check=True)
            env = dict(os.environ, LD_PRELOAD=str(library),
                       JAYDB_TEST_GPU_FAULT=str(fault), JAYDB_TEST_GPU_TRACE=str(trace))
            server = self.server(env=env)
            handle = self.register(server)
            private = next(Path(tempfile.gettempdir()).glob(f'jaydb2-{server.process.pid}-*'))
            native = next(private.glob('request-*/*.program'))
            device = Path(str(native)+'.gpu')
            self.assertTrue(device.is_file(), 'preparation must eagerly build GPU artifact')
            manifest = json.loads(Path(str(native)+'.json').read_text())
            self.assertTrue(manifest['hasBangs'])
            self.assertEqual(manifest['gpuMiB'], 512)
            self.assertEqual(manifest['backend'], 'cuda')
            # Preprocessors are unwrapped CPU executables and have no device bundle.
            self.assertFalse(list((private/'authenticate').glob('*.gpu')))
            trace.write_text('')
            self.execute(server, handle, 'alice-token', 'abc')
            events = trace.read_text().splitlines()
            self.assertIn('allocation 0', events)
            self.assertIn('launch 0', events, 'no successful real CUDA kernel launch')
            self.assertIn('sync 0', events)
            self.assertFalse(any(not event.endswith(' 0') for event in events))
            # Both files and all compilation/proof metadata are sealed.
            for path in [native, device, Path(str(native)+'.json'), native.parent/'checked.c',
                         native.parent/'Client.bend', native.parent/'ClientProof.bend']:
                original = path.read_bytes()
                for mutation in ['missing', 'substituted']:
                    try:
                        if mutation == 'missing': path.unlink()
                        else: path.write_bytes(original+b'substitute')
                        trace.write_text('')
                        self.assertEqual(server.prepared(1, handle, 'abc', 'never-published'),
                            {'status': 'failure', 'value': None}, server.diagnostics())
                        self.assertEqual(trace.read_text(), '', 'tampered bundle reached GPU')
                        if mutation == 'missing': self.assertFalse(path.exists())
                    finally:
                        path.write_bytes(original)
                        if path == native: path.chmod(0o700)
            self.assertIn('PREPARED_INTEGRITY', server.diagnostics())
            for kind, diagnostic in [('device', 'cuInit failed'), ('allocation', 'corpus reservation failed'),
                                     ('launch', 'device launch failed'), ('runtime', 'device fault')]:
                fault.write_text(kind)
                before = len(server.diagnostics())
                self.assertEqual(server.prepared(1, handle, 'abc', 'never-published'),
                    {'status': 'failure', 'value': None}, server.diagnostics())
                self.assertIn(diagnostic, server.diagnostics()[before:])
                fault.unlink()
                # A fresh child still sees old credentials, including after a
                # failure at the GPU bang following the private credential write.
                self.execute(server, handle, 'abc', 'abc')
            # Ordinary device failure cannot register anything or mutate state.
            fault.write_text('device')
            self.assertEqual(server.call(CODE, CONCRETE, 'abc', 'never-published'),
                {'status': 'failure', 'value': None}, server.diagnostics())
            self.assertIn('GPU_BUILD', server.diagnostics())
            fault.unlink()
            self.execute(server, handle, 'abc', 'abc')
            server.finish()

    def test_unwrapped_unavailable_device_has_no_auto_fallback(self):
        env = dict(os.environ, CUDA_VISIBLE_DEVICES='')
        server = self.server(env=env)
        self.assertEqual(server.prepared(0, CODE, 'alice-token', proof=PROOF),
            {'status': 'failure', 'value': None}, server.diagnostics())
        self.assertIn('GPU_BUILD', server.diagnostics())
        # Fresh authentication remains ahead of build/unavailable-device errors.
        self.assertEqual(server.prepared(0, CODE, 'invalid', proof=PROOF),
            {'status': 'authentication', 'value': None})
        server.finish()
        cpu = self.server(gpu=False, env=env)
        handle = self.register(cpu)
        self.execute(cpu, handle, 'alice-token', 'x')
        cpu.finish()


if __name__ == '__main__':
    unittest.main(verbosity=2)
