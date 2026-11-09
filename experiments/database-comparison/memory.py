"""Sample Linux process-tree RSS, including children spawned by worker threads.

RSS is summed across processes: shared pages can be counted more than once, and
10 ms sampling can miss short peaks. This measures observed process memory,
not database-only allocations or a memory bound. When the root is the benchmark
Python process (SQLite), client/oracle/interpreter memory is included too.
"""
from __future__ import annotations

import errno
from pathlib import Path
import threading


_GONE = (errno.ENOENT, errno.ESRCH)
_INTERVAL_MS = 10


def _read(path: Path) -> str | None:
    try:
        return path.read_text()
    except OSError as exc:
        # A process or task can disappear between discovery and any /proc read.
        if exc.errno in _GONE:
            return None
        raise


def _identity(pid: int) -> str | None:
    stat = _read(Path('/proc') / str(pid) / 'stat')
    if stat is None:
        return None
    # comm may contain spaces and parentheses. The last ')' ends the field;
    # starttime is stat field 22, i.e. index 19 following field 2 (comm).
    fields = stat[stat.rfind(')') + 1:].split()
    if len(fields) <= 19:
        raise ValueError(f'Malformed /proc/{pid}/stat')
    return fields[19]


def _rss(pid: int) -> int:
    status = _read(Path('/proc') / str(pid) / 'status')
    if status is None:
        return 0
    for line in status.splitlines():
        if line.startswith('VmRSS:'):
            parts = line.split()
            if len(parts) != 3 or parts[2] != 'kB':
                raise ValueError(f'Unexpected VmRSS format for process {pid}: {line!r}')
            return int(parts[1]) * 1024
    # Zombies and kernel tasks have no resident userspace memory field.
    return 0


def _children(pid: int) -> set[int]:
    result = set()
    tasks = Path('/proc') / str(pid) / 'task'
    try:
        entries = list(tasks.iterdir())
    except OSError as exc:
        if exc.errno in _GONE:
            return result
        raise
    for entry in entries:
        data = _read(entry / 'children')
        if data:
            result.update(int(child) for child in data.split())
    return result


def _tree_rss(pid: int, identity: str | None) -> int:
    if identity is None or _identity(pid) != identity:
        # Do not attach to an unrelated process if the original root PID exits
        # and the kernel reuses its number before sampling stops.
        return 0
    total, pending, visited = 0, [pid], set()
    while pending:
        current = pending.pop()
        if current in visited:
            continue
        visited.add(current)
        total += _rss(current)
        pending.extend(_children(current) - visited)
    return total


class Memory:
    """One-use sampler for a root process plus its living descendants.

    start() samples a baseline synchronously and begins the background sampler.
    stop() joins it, samples once more, and returns serializable byte counters.
    Disappearing processes are normal; permission, format and other errors are
    raised at start() or propagated by stop(), never silently discarded.
    """

    def __init__(self, pid: int):
        if type(pid) is not int or pid <= 0:
            raise ValueError('A positive integer process ID is required')
        self.pid = pid
        self._event = threading.Event()
        self._thread = None
        self._identity = None
        self._baseline = self._peak = self._last = self._samples = 0
        self._error = None
        self._result = None

    def _sample(self):
        value = _tree_rss(self.pid, self._identity)
        self._last = value
        self._peak = max(self._peak, value)
        self._samples += 1
        return value

    def _run(self):
        try:
            while not self._event.wait(_INTERVAL_MS / 1000):
                self._sample()
        except Exception as exc:
            self._error = exc
            self._event.set()

    def start(self):
        if self._thread is not None or self._result is not None:
            raise RuntimeError('A memory sampler can only be started once')
        self._identity = _identity(self.pid)
        self._baseline = self._sample()
        self._thread = threading.Thread(target=self._run, name=f'rss-tree-{self.pid}', daemon=True)
        self._thread.start()
        return self

    def stop(self) -> dict:
        if self._result is not None:
            return dict(self._result)
        if self._thread is None:
            raise RuntimeError('Start the memory sampler before stopping it')
        self._event.set()
        self._thread.join(timeout=5)
        if self._thread.is_alive():
            raise RuntimeError(f'Memory sampler for PID {self.pid} failed to stop')
        if self._error is not None:
            raise RuntimeError(f'Memory sampler for PID {self.pid} failed: {self._error}') from self._error
        self._sample()
        self._result = {
            'observed_peak_tree_rss_bytes': self._peak,
            'baseline_tree_rss_bytes': self._baseline,
            'last_tree_rss_bytes': self._last,
            'samples': self._samples,
            'interval_ms': _INTERVAL_MS,
            'root_pid': self.pid,
            'metric': 'Sum of VmRSS across root process and living descendants; shared pages counted per process',
        }
        return dict(self._result)
