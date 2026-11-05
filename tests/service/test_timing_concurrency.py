"""Actual per-worker timing with controlled completion and failed delivery."""
import json
import os
from pathlib import Path
import select
import socket
import subprocess
import tempfile
import time
import unittest

from tests.service.test_concurrency import CODE, PROOF
from tests.service.test_end_to_end import ROOT, Server
from tests.service.test_prepared import universal_access_proof
from tools.client import prepared_frame, unframe


class TimingConcurrencyTests(unittest.TestCase):
    def test_distinct_reads_log_completion_before_fifo_delivery_and_after_channel_failure(self):
        scratch = ROOT/'build/timing'
        scratch.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix='read-gate-', dir=scratch) as temporary:
            directory = Path(temporary)
            library = directory/'gate.so'
            subprocess.run(['cc', '-shared', '-fPIC', str(ROOT/'tests/service/read_gate.c'),
                            '-o', str(library), '-ldl'], check=True)
            gatepath = (directory/'g').relative_to(ROOT)
            gate = socket.socket(socket.AF_UNIX)
            self.addCleanup(gate.close)
            gate.bind(str(gatepath))
            gate.listen(16)
            gate.settimeout(30)
            targets, log = directory/'targets', directory/'timing.ndjson'
            targets.write_text('')
            env = dict(os.environ, LD_PRELOAD=str(library), JAYDB_TEST_READ_GATE=str(gatepath),
                       JAYDB_TEST_READ_TARGETS=str(targets), BENDRTS='--gpu-build --help')
            server = Server(ROOT/'examples/credential-exchange', env=env, threads=2,
                options=['--read-workers', '2', '--timing-log', str(log),
                         '--storage', str(directory/'db'), '--storage-mode', 'create'])
            self.addCleanup(server.close)
            code2 = CODE + '\n# Distinct source and executable path for second queued read.\n'
            reads = [server.prepared(3, code, 'alice-token', proof=PROOF) for code in (CODE, code2)]
            for read in reads:
                self.assertEqual(read['status'], 'prepared', server.diagnostics())
            folder = ROOT/'examples/credential-exchange'
            writecode = (folder/'Client.bend').read_text()
            writeproof = universal_access_proof((folder/'ClientProof.bend').read_text())
            write = server.prepared(0, writecode, 'alice-token', proof=writeproof)
            self.assertEqual(write['status'], 'prepared', server.diagnostics())
            private = next(Path(tempfile.gettempdir()).glob(f'jaydb2-{server.process.pid}-*'))
            programs = {code: next(p.glob('*.program')) for p in private.glob('request-*')
                        if (code := (p/'Client.bend').read_text()) in (CODE, code2, writecode)}
            self.assertEqual(len(set(programs.values())), 3)
            targets.write_text(''.join(str(path)+'\n' for path in programs.values()))

            def held():
                connection, _ = gate.accept()
                self.addCleanup(connection.close)
                connection.settimeout(30)
                pid, path = connection.recv(4200).decode().strip().split(' ', 1)
                self.assertTrue(Path('/proc', pid).exists())
                return Path(path), connection

            def release(connection):
                connection.sendall(b'r')
                connection.close()

            def response():
                header = server.read(8)
                return unframe(header+server.read(int.from_bytes(header, 'big')))

            def records():
                return [json.loads(line) for line in log.read_text().splitlines()]

            def wait_for(sequence):
                deadline = time.monotonic()+30
                while time.monotonic() < deadline:
                    entries = {entry['sequence']: entry for entry in records()}
                    if sequence in entries:
                        return entries
                    time.sleep(0.01)  # Bounded CI observation; no service scheduling change.
                self.fail(f'no timing completion {sequence}: {records()}\n{server.diagnostics()}')

            def send(messages):
                server.process.stdin.write(b''.join(messages))
                server.process.stdin.flush()

            first_id = len(records())+1
            # Credential exchange is exclusive. Hold its checked native process
            # until both reads are queued, then both authenticate as Bob against
            # the changed root (the same credential previously identified Alice).
            send([prepared_frame(1, write['value'], 'alice-token'),
                  prepared_frame(1, reads[0]['value'], 'alice-token', 11),
                  prepared_frame(1, reads[1]['value'], 'alice-token', 22)])
            path, writer = held()
            self.assertEqual(path, programs[writecode])
            release(writer)
            self.assertEqual(response(), {'status':'success', 'value':'bob-token'})
            held_reads = dict([held(), held()])
            self.assertEqual(set(held_reads), {programs[CODE], programs[code2]})
            release(held_reads[programs[code2]])
            complete = wait_for(first_id+2)
            self.assertNotIn(first_id+1, complete, 'first queued read must still be held')
            self.assertEqual(complete[first_id]['principal'], 'alice')
            self.assertEqual(complete[first_id+2]['principal'], 'bob')
            self.assertTrue(complete[first_id+2]['read_batch'])
            self.assertFalse(select.select([server.process.stdout], [], [], 0)[0],
                             'second response bypassed held first read')
            release(held_reads[programs[CODE]])
            self.assertEqual(response(), {'status':'success', 'value':11})
            self.assertEqual(response(), {'status':'success', 'value':22})
            wait_for(first_id+1)

            # A second exclusive exchange gates two queued reads plus a later
            # exclusive operation. Close actual client output with both live.
            first_id = len(records())+1
            send([prepared_frame(1, write['value'], 'alice-token', ['alice-token', 'bob-token']),
                  prepared_frame(1, reads[0]['value'], 'alice-token', 33),
                  prepared_frame(1, reads[1]['value'], 'alice-token', 44),
                  prepared_frame(1, write['value'], 'alice-token')])
            path, writer = held()
            self.assertEqual(path, programs[writecode])
            release(writer)
            self.assertEqual(response(), {'status':'success', 'value':'bob-token'})
            held_reads = dict([held(), held()])
            self.assertEqual(set(held_reads), {programs[CODE], programs[code2]})
            server.process.stdout.close()
            release(held_reads[programs[CODE]])
            wait_for(first_id+1)
            self.assertIsNone(server.process.poll(), 'later active read was abandoned')
            release(held_reads[programs[code2]])
            self.assertEqual(server.process.wait(timeout=30), 0, server.diagnostics())
            complete = {entry['sequence']:entry for entry in records()}
            self.assertEqual(set(complete), set(range(1, first_id+3)))
            self.assertEqual(complete[first_id+1]['principal'], 'alice')
            self.assertEqual(complete[first_id+2]['principal'], 'alice')
            self.assertTrue(all(int(entry['elapsed_ns']) > 0 for entry in complete.values()))
            gate.settimeout(0.1)
            with self.assertRaises(socket.timeout):
                gate.accept()  # No queued exclusive executable launched.
