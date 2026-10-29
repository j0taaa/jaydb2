"""Synchronous compiler helper owner, for the trusted serial Linux entry."""
import os
import signal
import subprocess

from .loading import OwnershipError


class ProcessOwner:
    def __init__(self, command):
        self._busy = self._uncertain = self._finished = self._closed = False
        self._process = subprocess.Popen(command, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, start_new_session=True,
            env={**os.environ, 'BEND_NO_TELEMETRY': '1'})

    @property
    def stdout(self):
        return self._process.stdout

    @property
    def stderr(self):
        return self._process.stderr

    @property
    def returncode(self):
        return self._process.returncode

    def poll(self):
        """Observe without reaping: the child pins its process-group identity."""
        if self._uncertain or self._busy or self._closed:
            raise OwnershipError('Helper is closed, uncertain or already in use')
        if self._finished:
            return True
        try:
            return os.waitid(os.P_PID, self._process.pid,
                             os.WEXITED | os.WNOHANG | os.WNOWAIT) is not None
        except BaseException as error:
            self._uncertain = True
            raise OwnershipError('Helper wait ownership is uncertain') from error

    def stop_and_wait(self):
        if self._uncertain or self._busy:
            raise OwnershipError('Cannot retry uncertain helper cleanup')
        if self._finished:
            return
        self._busy = True
        self._uncertain = True
        try:
            # Check that this is still our unreaped child BEFORE killpg. No
            # other waiter is allowed in the selected host profile.
            os.waitid(os.P_PID, self._process.pid,
                      os.WEXITED | os.WNOHANG | os.WNOWAIT)
            try:
                os.killpg(self._process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass  # the group has already ended; the child is still pinned
            self._process.wait()
            self._finished = True
            self._uncertain = False
        except BaseException as error:
            raise OwnershipError('Helper cleanup is uncertain; never retry') from error
        finally:
            self._busy = False

    def close(self):
        if self._closed:
            return
        self.stop_and_wait()
        # FileIO.close consumes its fd even if close reports an error on
        # Linux. Never retry a numeric descriptor after an exceptional close.
        self._closed = True
        try:
            try:
                self.stdout.close()
            finally:
                self.stderr.close()
        except BaseException as error:
            raise OwnershipError('Helper pipe cleanup failed; stop the instance') from error

    def __enter__(self):
        return self

    def __exit__(self, *exception):
        self.close()
