"""Observer and diagnostic failures cannot replace ordinary client outcomes."""
import json
import os
import signal
from pathlib import Path
import socket
import subprocess
import tempfile
import unittest

from tests.service.test_end_to_end import ROOT
from tests.service.test_persistence import state_bytes
from tools.client import frame, unframe


def responses(raw):
    result = []
    while raw:
        assert len(raw) >= 8
        size = 8 + int.from_bytes(raw[:8], 'big')
        assert size <= len(raw)
        result.append(unframe(raw[:size])); raw = raw[size:]
    return result


class ObserverTests(unittest.TestCase):
    def test_failed_timing_and_stderr_preserve_durable_commit_and_next_response(self):
        folder = ROOT/'examples/access'
        code, proof = ((folder/name).read_text() for name in ('Client.bend', 'ClientProof.bend'))
        with tempfile.TemporaryDirectory(prefix='jaydb-observer-', dir='/tmp') as directory:
            storage = Path(directory)/'db'
            requests = frame(dict(code=code, proof=proof, credential='alice-token', arguments='observed-new'))
            requests += frame(dict(code='', proof='', credential='alice-token', arguments=None))
            with open('/dev/full', 'wb') as diagnostics:
                with subprocess.Popen([str(ROOT/'jaydb2'), '--threads', '1',
                    '--configuration', str(folder/'Configuration.bend'), '--seed', str(folder/'Seed.bend'),
                    '--storage', str(storage), '--storage-mode', 'create', '--timing-log', '/dev/full'],
                    stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=diagnostics,
                    start_new_session=True, cwd=ROOT) as process:
                    try:
                        output, _ = process.communicate(requests, timeout=180)
                    finally:
                        if process.poll() is None:
                            os.killpg(process.pid, signal.SIGKILL); process.wait(timeout=10)
            self.assertEqual(process.returncode, 0)
            self.assertEqual(responses(output), [dict(status='success', value='observed-new'),
                                                    dict(status='authentication', value=None)])
            self.assertIn(b'observed-new', state_bytes(storage))
            self.assertNotIn(b'alice-token', state_bytes(storage))

    def test_disconnected_inspector_and_failed_stderr_preserve_responses(self):
        folder = ROOT/'examples/access'
        with tempfile.TemporaryDirectory(prefix='jaydb-observer-', dir='/tmp') as directory:
            endpoint = str(Path(directory)/'socket')
            with socket.socket(socket.AF_UNIX) as listener, open('/dev/full', 'wb') as diagnostics:
                listener.bind(endpoint); listener.listen(1); listener.settimeout(180)
                process = subprocess.Popen([str(ROOT/'jaydb2'), '--threads', '1',
                    '--configuration', str(folder/'Configuration.bend'), '--seed', str(folder/'Seed.bend'),
                    '--inspect-socket', endpoint], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                    stderr=diagnostics, start_new_session=True, cwd=ROOT)
                try:
                    peer, _ = listener.accept()
                    with peer:
                        peer.settimeout(180)
                        def read(n):
                            data = bytearray()
                            while len(data) < n:
                                chunk = peer.recv(n-len(data)); self.assertTrue(chunk); data.extend(chunk)
                            return bytes(data)
                        def packet():
                            return read(int.from_bytes(read(8), 'big'))
                        self.assertEqual(json.loads(packet())['event'], 'initialized')
                        self.assertTrue(packet())
                        peer.shutdown(socket.SHUT_RDWR)
                    request = frame(dict(code='', proof='', credential='invalid', arguments=None))
                    output, _ = process.communicate(request+request, timeout=180)
                    self.assertEqual(process.returncode, 0)
                    self.assertEqual(responses(output), [dict(status='authentication', value=None)]*2)
                finally:
                    if process.poll() is None:
                        os.killpg(process.pid, signal.SIGKILL); process.wait(timeout=10)
                    for stream in (process.stdin, process.stdout):
                        stream.close()
