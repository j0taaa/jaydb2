"""Owned demo process groups survive their leader until explicit cleanup."""
import os
from pathlib import Path
import select
import signal
import subprocess
import sys
import threading
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from demo.server import Session, Unavailable


class DemoLifecycleTests(unittest.TestCase):
    def session(self, source):
        launch = subprocess.Popen

        def worker(*_args, **_kwargs):
            return launch([sys.executable, '-c', source], stdin=subprocess.PIPE,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          start_new_session=True)

        with patch('demo.server.subprocess.Popen', worker):
            session = Session()
        self.addCleanup(session.close)
        return session

    def running(self, pid):
        try:
            # An orphan may briefly remain a zombie under the host's init;
            # it has released its descriptors and cannot do more work.
            return Path(f'/proc/{pid}/stat').read_text().rpartition(') ')[2].split()[0] != 'Z'
        except FileNotFoundError:
            return False

    def descendant(self, session):
        pid = int(session.process.stdout.readline())

        def cleanup():
            if self.running(pid):
                try:
                    os.kill(pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            session.error_thread.join(timeout=5)

        self.addCleanup(cleanup)
        return pid

    def assert_closed(self, session, descendant):
        self.assertIsNotNone(session.process.returncode)
        self.assertFalse(session.error_thread.is_alive(), 'Descendant retained the stderr pipe after close')
        self.assertFalse(session.inspection_thread.is_alive())
        self.assertFalse(self.running(descendant), 'Owned descendant survived session cleanup')

    def test_exited_leader_keeps_ownership_until_descendant_cleanup(self):
        session = self.session(
            'import subprocess, sys\n'
            'p = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(30)"])\n'
            'print(p.pid, flush=True)\n')
        descendant = self.descendant(session)
        # Observe the real exit without releasing the PID/process-group anchor.
        os.waitid(os.P_PID, session.process.pid, os.WEXITED | os.WNOWAIT)
        self.assertIsNone(session.process.returncode)
        self.assertFalse(session.snapshot()['alive'])
        self.assertIsNone(session.process.returncode, 'Liveness inspection reaped the group owner')
        with self.assertRaises(Unavailable):
            session._call('', '', '', None)
        self.assertIsNone(session.process.returncode, 'Rejected submission reaped the group owner')
        session.close()
        self.assert_closed(session, descendant)

    def test_active_leader_cleanup_also_stops_its_descendant(self):
        session = self.session(
            'import subprocess, sys\n'
            'p = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(30)"])\n'
            'print(p.pid, flush=True)\n'
            'sys.stdin.buffer.read()\n')
        descendant = self.descendant(session)
        self.assertTrue(session.snapshot()['alive'])
        session.close()
        self.assert_closed(session, descendant)

    def test_stalled_active_leader_and_descendant_are_killed_after_grace(self):
        session = self.session(
            'import subprocess, sys, time\n'
            'p = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(30)"])\n'
            'print(p.pid, flush=True)\n'
            'time.sleep(30)\n')
        descendant = self.descendant(session)
        self.assertTrue(session.snapshot()['alive'])
        signal_group = os.killpg
        with patch('demo.server.CLOSE_TIMEOUT', 0.05), patch('demo.server.os.killpg', wraps=signal_group) as signals:
            session.close()
            session.close()
        signals.assert_called_once_with(session.process.pid, signal.SIGKILL)
        self.assertEqual(session.process.returncode, -signal.SIGKILL)
        self.assert_closed(session, descendant)

    def test_close_is_idempotent_and_never_signals_a_reaped_groups_reused_number(self):
        session = self.session('print("ready", flush=True)')
        self.assertEqual(session.process.stdout.readline(), b'ready\n')
        session.process.wait(timeout=5)
        # A separate real group stands in for a reused numeric group ID. The
        # already-reaped Popen must never be used as signal authority.
        unrelated = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(30)'],
                                     start_new_session=True)
        self.addCleanup(lambda: unrelated.wait(timeout=5))
        self.addCleanup(unrelated.kill)
        session.process.pid = unrelated.pid
        signal_group = os.killpg
        with patch('demo.server.os.killpg', wraps=signal_group) as signals:
            session.close()
            session.close()
        signals.assert_not_called()
        self.assertIsNone(unrelated.poll())

    def test_every_observer_thread_start_failure_closes_the_real_process_group(self):
        for failing_start in (1, 2):
            with self.subTest(failing_start=failing_start):
                session = Session.__new__(Session)
                threads = []
                descendant = None
                descendant_exit = None
                launch = subprocess.Popen
                failure = RuntimeError('injected observer thread start failure')

                def worker(*_args, **_kwargs):
                    nonlocal descendant, descendant_exit
                    process = launch([
                        sys.executable, '-c',
                        'import subprocess, sys\n'
                        'p = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(30)"])\n'
                        'print(p.pid, flush=True)\n'
                        'sys.stdin.buffer.read()\n'],
                        stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                        stderr=subprocess.PIPE, start_new_session=True)
                    descendant = int(process.stdout.readline())
                    descendant_exit = os.pidfd_open(descendant)
                    return process

                def observer_thread(*args, **kwargs):
                    thread = threading.Thread(*args, **kwargs)
                    threads.append(thread)
                    if len(threads) == failing_start:
                        def fail_start():
                            raise failure
                        thread.start = fail_start
                    return thread

                # Cleanup must also work against the broken constructor, so
                # the failing regression cannot strand its real processes.
                def cleanup():
                    if session.process.returncode is None:
                        try:
                            os.killpg(session.process.pid, signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                        session.process.wait(timeout=5)
                    if descendant is not None and self.running(descendant):
                        try:
                            os.kill(descendant, signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                    session.listener.close()
                    for thread in threads:
                        if thread.ident is not None:
                            thread.join(timeout=5)
                    for pipe in (session.process.stdin, session.process.stdout, session.process.stderr):
                        pipe.close()
                    session.directory.cleanup()
                    if descendant_exit is not None:
                        os.close(descendant_exit)

                # Patch the demo's namespace only. All created threads and
                # subprocess pipes are real, including the first live observer
                # when starting the second observer fails.
                local_threading = SimpleNamespace(RLock=threading.RLock,
                                                  Condition=threading.Condition,
                                                  Thread=observer_thread)
                try:
                    with patch('demo.server.threading', local_threading), patch('demo.server.subprocess.Popen', worker):
                        with self.assertRaises(RuntimeError) as raised:
                            Session.__init__(session)
                    self.assertIs(raised.exception, failure, 'Cleanup masked the original start failure')
                    self.assertIsNotNone(session.process.returncode, 'Failed construction left its real child unreaped')
                    # With no stderr reader started, there is no reader join
                    # to await SIGKILL delivery. Observe the actual descendant
                    # exit instead of racing its scheduler through /proc.
                    self.assertEqual(select.select([descendant_exit], [], [], 5)[0], [descendant_exit])
                    self.assertFalse(self.running(descendant), 'Failed construction left a descendant running')
                    self.assertTrue(session.closed, 'Failed construction abandoned its owned session')
                    self.assertTrue(all(not thread.is_alive() for thread in threads))
                    self.assertTrue(session.process.stdin.closed)
                    self.assertTrue(session.process.stdout.closed)
                    self.assertTrue(session.process.stderr.closed)
                    self.assertEqual(session.listener.fileno(), -1)
                    self.assertFalse(Path(session.directory.name).exists())
                    # Failed construction completed cleanup; another close has
                    # no authority to signal a stale numeric process group.
                    with patch('demo.server.os.killpg') as signals:
                        session.close()
                    signals.assert_not_called()
                finally:
                    cleanup()


if __name__ == '__main__':
    unittest.main(verbosity=2)
