"""Opt-in tests on a real NVIDIA GPU; no skip or synthetic GPU results.
Run under the experiment heavy lock. CPU default regressions live separately.
"""
import json
import os
from pathlib import Path
import subprocess
import socket
import threading
import tempfile
import unittest

from tests.service.test_end_to_end import ROOT, Server
from tools.client import prepared_frame, unframe

CODE = (ROOT/'experiments/gpu/Client.bend').read_text()
PROOF = (ROOT/'experiments/gpu/ClientProof.bend').read_text()
CONCRETE = (ROOT/'examples/access/ClientProof.bend').read_text()
HEAVY = (ROOT/'experiments/gpu/HeavyClient.bend').read_text()


def oracle(depth, rounds=64):
    total = 0
    for seed in range(1 << depth):
        x = seed
        for _ in range(rounds):
            x = ((x ^ (x >> 16))*1664525 + 1013904223) & 0xffffffff
        total = (total + x) & 0xffffffff
    return total


class StateFeed:
    """Read the existing administrator socket, with no worker instrumentation."""
    def __init__(self, path):
        self.listener = socket.socket(socket.AF_UNIX)
        self.listener.bind(str(path))
        self.listener.listen(1)
        self.states, self.events, self.errors = [], [], []
        self.thread = threading.Thread(target=self.read, daemon=True)
        self.thread.start()

    def read(self):
        try:
            with self.listener.accept()[0] as stream:
                def exact(n):
                    data = bytearray()
                    while len(data) < n:
                        part = stream.recv(n-len(data))
                        if not part:
                            if data: raise AssertionError('truncated inspector frame')
                            return None
                        data.extend(part)
                    return bytes(data)
                def frame():
                    head = exact(8)
                    return None if head is None else head+exact(int.from_bytes(head, 'big'))
                while (metadata := frame()) is not None:
                    state = frame()
                    if state is None: raise AssertionError('inspector omitted state')
                    self.states.append(unframe(state))
                    self.events.append(unframe(metadata))
        except Exception as error:
            self.errors.append(str(error))

    def finish(self):
        self.thread.join(timeout=5)
        self.listener.close()
        if self.thread.is_alive() or self.errors:
            raise AssertionError(f'inspector failure: {self.errors}')


class GpuTests(unittest.TestCase):
    def test_bad_proof_never_compiles_or_enters_cuda_or_publishes(self):
        with tempfile.TemporaryDirectory(prefix='gpu-reject-') as tmp:
            folder = Path(tmp)
            library, trace = folder/'faults.so', folder/'trace'
            subprocess.run(['gcc', '-shared', '-fPIC', str(ROOT/'tests/service/gpu_faults.c'),
                            '-o', str(library), '-ldl'], check=True)
            trace.write_text('')
            feed = StateFeed(folder/'admin.sock')
            env = dict(os.environ, LD_PRELOAD=str(library), JAYDB_TEST_GPU_TRACE=str(trace),
                       JAYDB_BENCH_TIMING='1')
            server = self.server(env=env, options=['--inspect-socket', str(folder/'admin.sock')])
            # Wait until CPU initialization has completed before recording the boundary.
            self.assertEqual(server.call(CODE, CONCRETE, 'invalid'),
                             {'status': 'authentication', 'value': None})
            start = len(server.diagnostics())
            bad = PROOF + '\nlaw false:\n  {False{} == True{} : Bool}\ndef false(): {==}\n'
            for prepared in [False, True]:
                result = (server.prepared(0, CODE, 'alice-token', proof=bad) if prepared
                          else server.call(CODE, bad, 'alice-token', 'never-published'))
                self.assertEqual(result, {'status': 'certificate', 'value': None}, server.diagnostics())
            errors = server.diagnostics()[start:]
            self.assertIn('PRIMARY_CHECK', errors)
            self.assertNotIn('c_compilation', errors)
            self.assertNotIn('c_emission', errors)
            self.assertEqual(trace.read_text(), '', 'bad proof reached the CUDA driver')
            private = next(Path(tempfile.gettempdir()).glob(f'jaydb2-{server.process.pid}-*'))
            self.assertFalse(list(private.glob('request-*')), 'rejected artifacts/registration survived')
            server.finish()
            feed.finish()
            self.assertTrue(feed.states)
            self.assertTrue(all(state == feed.states[0] for state in feed.states), 'rejection published state')

    def test_pipelined_gpu_execution_timing_and_durable_reopen(self):
        with tempfile.TemporaryDirectory(prefix='gpu-durable-') as tmp:
            folder = Path(tmp)
            log, storage = folder/'timing.ndjson', folder/'db'
            common = ['--storage', str(storage), '--timing-log', str(log)]
            server = self.server(options=[*common, '--storage-mode', 'create'])
            handle = self.register(server)
            server.process.stdin.write(prepared_frame(1, handle, 'alice-token', 'ab') +
                                       prepared_frame(1, handle, 'ab', 'abc'))
            server.process.stdin.flush()
            for depth in [2, 3]:
                header = server.read(8)
                self.assertEqual(unframe(header + server.read(int.from_bytes(header, 'big'))),
                                 {'status': 'success', 'value': oracle(depth)}, server.diagnostics())
            server.finish()
            records = [json.loads(line) for line in log.read_text().splitlines()]
            self.assertEqual([r['sequence'] for r in records], [1, 2, 3])
            reopened = Server(ROOT/'examples/access', seed=False, options=[
                '--threads', '1', '--gpu', '512', *common, '--storage-mode', 'open'])
            self.addCleanup(reopened.close)
            self.assertEqual(reopened.prepared(1, handle, 'abc', 'x'),
                             {'status': 'failure', 'value': None}, reopened.diagnostics())
            receipt = reopened.prepared(0, CODE, 'abc', proof=PROOF)
            self.assertEqual(receipt['status'], 'prepared', reopened.diagnostics())
            self.execute(reopened, receipt['value'], 'abc', 'x')
            reopened.finish()

    def server(self, gpu=True, env=None, options=()):
        server = Server(ROOT/'examples/access', env=env,
                        options=['--threads', '1', '--gpu', '512' if gpu else 'off', *options])
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
        snapshots, source_hashes = [], []
        for gpu in [False, True]:
            with self.subTest(gpu=gpu):
                folder = tempfile.TemporaryDirectory(prefix='gpu-inspector-')
                self.addCleanup(folder.cleanup)
                path = Path(folder.name)/'admin.sock'
                feed = StateFeed(path)
                server = self.server(gpu, env=dict(os.environ, BENDRTS='--gpu-build'),
                                     options=['--inspect-socket', str(path)])
                small = 's'
                self.assertEqual(server.call(CODE, CONCRETE, 'alice-token', small),
                    {'status': 'success', 'value': oracle(len(small))}, server.diagnostics())
                self.assertEqual(server.call(CODE, CONCRETE, 'alice-token', 'old'),
                    {'status': 'authentication', 'value': None})
                receipt = server.prepared(0, CODE, small, proof=PROOF)
                self.assertEqual(receipt['status'], 'prepared', server.diagnostics())
                handle = receipt['value']
                private = next(Path(tempfile.gettempdir()).glob(f'jaydb2-{server.process.pid}-*'))
                native, = private.glob('request-*/*.program')
                source_hashes.append(json.loads(Path(str(native)+'.json').read_text())['sourceSha256'])
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
                feed.finish()
                snapshots.append(feed.states)
        self.assertEqual(source_hashes[0], source_hashes[1], 'CPU and CUDA used different emitted C bytes')
        self.assertEqual(snapshots[0], snapshots[1], 'CPU and GPU publications differ')
        self.assertGreater(len(snapshots[0]), 10)
        self.assertEqual(snapshots[0][-1], {'tables': [], 'users': [
            {'credential': 'x', 'id': 'alice', 'kind': 'user'},
            {'credential': 'bob-token', 'id': 'bob', 'kind': 'user'}]})

    def test_bundle_integrity_real_launches_and_failure_rollback(self):
        with tempfile.TemporaryDirectory(prefix='gpu-faults-') as tmp:
            folder = Path(tmp)
            library, fault, trace = folder/'faults.so', folder/'fault', folder/'trace'
            server_env_path = folder/'bundle-path'
            subprocess.run(['gcc', '-shared', '-fPIC', str(ROOT/'tests/service/gpu_faults.c'),
                            '-o', str(library), '-ldl'], check=True)
            env = dict(os.environ, LD_PRELOAD=str(library),
                       JAYDB_TEST_GPU_FAULT=str(fault), JAYDB_TEST_GPU_TRACE=str(trace),
                       JAYDB_TEST_GPU_BUNDLE_PATH=str(server_env_path))
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
            print('CUDA forwarding evidence: ' + json.dumps({
                'sourceSha256': manifest['sourceSha256'], 'hasBangs': manifest['hasBangs'],
                'allocation_successes': events.count('allocation 0'),
                'launch_successes': events.count('launch 0'),
                'synchronize_successes': events.count('sync 0')}), flush=True)
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
            # Mutate only after the host's pre-execution integrity gate. A real
            # runtime rebuild (even if byte-identical) or a post-launch changed
            # cubin must discard the otherwise successful private proposal.
            original_device = device.read_bytes()
            for kind in ['rebuild', 'changed']:
                try:
                    fault.write_text(kind)
                    server_env_path.write_text(str(device))
                    before = len(server.diagnostics())
                    self.assertEqual(server.prepared(1, handle, 'abc', 'never-published'),
                                     {'status': 'failure', 'value': None}, server.diagnostics())
                    self.assertTrue(any(message in server.diagnostics()[before:] for message in
                                        ['GPU_REBUILD', 'missing or changed artifact']))
                finally:
                    fault.unlink(missing_ok=True)
                    device.write_bytes(original_device)
                self.execute(server, handle, 'abc', 'abc')
            # Ordinary device failure cannot register anything or mutate state.
            fault.write_text('device')
            self.assertEqual(server.call(CODE, CONCRETE, 'abc', 'never-published'),
                {'status': 'failure', 'value': None}, server.diagnostics())
            self.assertIn('GPU_BUILD', server.diagnostics())
            fault.unlink()
            self.execute(server, handle, 'abc', 'abc')
            # Attest the benchmark's HeavyClient too, using a small scalar oracle.
            receipt = server.prepared(0, HEAVY, 'abc', proof=PROOF)
            self.assertEqual(receipt['status'], 'prepared', server.diagnostics())
            heavy_native, = [candidate for candidate in private.glob('request-*/*.program')
                             if (candidate.parent/'Client.bend').read_text() == HEAVY]
            heavy_report = json.loads(Path(str(heavy_native)+'.json').read_text())
            self.assertTrue(heavy_report['hasBangs'])
            trace.write_text('')
            self.assertEqual(server.prepared(1, receipt['value'], 'abc', 'xx'),
                             {'status': 'success', 'value': oracle(2, 8192)}, server.diagnostics())
            heavy_events = trace.read_text().splitlines()
            self.assertIn('launch 0', heavy_events)
            self.assertIn('sync 0', heavy_events)
            print('HeavyClient forwarding evidence: ' + json.dumps({
                'sourceSha256': heavy_report['sourceSha256'], 'hasBangs': True,
                'launch_successes': heavy_events.count('launch 0'),
                'synchronize_successes': heavy_events.count('sync 0')}), flush=True)
            server.finish()

    def test_unwrapped_unavailable_device_has_no_auto_fallback(self):
        env = dict(os.environ, CUDA_VISIBLE_DEVICES='')
        with tempfile.TemporaryDirectory(prefix='gpu-unavailable-') as tmp:
            path = Path(tmp)/'admin.sock'
            feed = StateFeed(path)
            server = self.server(env=env, options=['--inspect-socket', str(path)])
            self.assertEqual(server.prepared(0, CODE, 'alice-token', proof=PROOF),
                {'status': 'failure', 'value': None}, server.diagnostics())
            self.assertEqual(server.call(CODE, CONCRETE, 'alice-token', 'never-published'),
                {'status': 'failure', 'value': None}, server.diagnostics())
            self.assertIn('GPU_BUILD', server.diagnostics())
            # Fresh authentication remains ahead of unavailable-device errors.
            self.assertEqual(server.prepared(0, CODE, 'invalid', proof=PROOF),
                {'status': 'authentication', 'value': None})
            server.finish()
            feed.finish()
            self.assertGreaterEqual(len(feed.states), 4)
            self.assertTrue(all(state == feed.states[0] for state in feed.states),
                            'unavailable CUDA device published state')
        cpu = self.server(gpu=False, env=env)
        handle = self.register(cpu)
        self.execute(cpu, handle, 'alice-token', 'x')
        cpu.finish()


if __name__ == '__main__':
    unittest.main(verbosity=2)
