"""Adapter watchdog checks with real pipes and controlled subprocess readers."""
import fcntl
import subprocess
import sys
import threading
import time
import unittest
from unittest.mock import patch

from demo.server import Session, Unavailable


class DemoTransportTests(unittest.TestCase):
    def worker(self, source):
        process = subprocess.Popen([sys.executable, '-c', source],
                                   stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE)
        # Linux may otherwise fit an entire legal request in the pipe. Keep
        # this failure/control deterministic across kernel/user pipe defaults.
        fcntl.fcntl(process.stdin, fcntl.F_SETPIPE_SZ, 4096)

        def cleanup():
            if process.poll() is None:
                process.kill()
            process.wait(timeout=5)
            for pipe in (process.stdin, process.stdout, process.stderr):
                try:
                    pipe.close()
                except BrokenPipeError:
                    pass

        self.addCleanup(cleanup)
        session = Session.__new__(Session)
        session.process = process
        session.failed = False
        session.call_sequence = 0
        return session, cleanup

    def test_full_request_pipe_times_out_and_closes_without_retry(self):
        session, cleanup = self.worker('import sys; sys.stdin.buffer.read(0); import time; time.sleep(30)')
        closed = []
        result = []

        def close():
            closed.append(True)
            cleanup()

        session.close = close

        def call():
            try:
                session._call('x' * 24000, '', 'credential', None)
            except Exception as error:
                result.append(error)

        with patch('demo.server.CALL_TIMEOUT', 0.05):
            thread = threading.Thread(target=call)
            thread.start()
            thread.join(timeout=2)
            stopped = not thread.is_alive()
            # Clean up even if the regression returns: a broken write must
            # never leave the test runner itself blocked on a live thread.
            if not stopped:
                cleanup()
                thread.join(timeout=5)
        self.assertTrue(stopped, 'Request write bypassed the adapter watchdog')
        self.assertEqual(closed, [True])
        self.assertEqual(session.call_sequence, 1)
        self.assertEqual(len(result), 1)
        self.assertIsInstance(result[0], Unavailable)
        self.assertIn('Incomplete request or timeout', str(result[0]))
        self.assertIn('Outcome unknown; no automatic retry', str(result[0]))

    def test_partial_request_writes_deliver_exact_bytes_to_a_live_reader(self):
        data = bytes(range(256)) * 512
        session, _ = self.worker(
            'import sys\n'
            f'remaining = {len(data)}\n'
            'chunks = []\n'
            'while remaining:\n'
            '    chunk = sys.stdin.buffer.read(min(113, remaining))\n'
            '    if not chunk: raise SystemExit(2)\n'
            '    chunks.append(chunk)\n'
            '    remaining -= len(chunk)\n'
            'sys.stdout.buffer.write(b"".join(chunks))\n'
            'sys.stdout.buffer.flush()\n')
        deadline = time.monotonic() + 5
        session._write(data, deadline)
        self.assertEqual(session._read(len(data), deadline), data)
        self.assertEqual(session.process.wait(timeout=5), 0)


if __name__ == '__main__':
    unittest.main(verbosity=2)
