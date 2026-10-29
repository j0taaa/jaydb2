"""Exact compiler wall budgets; only each OS wait is converted to float."""
from decimal import Decimal, InvalidOperation
import subprocess
import time

WAIT_NS = 50_000_000


def parse_nat(text):
    if not isinstance(text, str) or not text or any(c < '0' or c > '9' for c in text):
        raise ValueError('Unsigned decimal integer required')
    value = 0
    for at in range(0, len(text), 9):
        chunk = text[at:at + 9]
        value = value * (10 ** len(chunk)) + int(chunk)
    return value


def format_nat(value):
    if not isinstance(value, int) or value < 0:
        raise ValueError('Natural integer required')
    if not value:
        return '0'
    pieces = []
    while value:
        value, part = divmod(value, 1_000_000_000)
        pieces.append(part)
    return str(pieces[-1]) + ''.join(f'{piece:09d}' for piece in reversed(pieces[:-1]))


def seconds_to_ns(value):
    try:
        seconds = Decimal(value) if isinstance(value, (int, Decimal)) else Decimal(str(value))
        if not seconds.is_finite() or seconds <= 0:
            raise ValueError('Positive finite compiler timeout required')
        numerator, denominator = seconds.as_integer_ratio()
    except (InvalidOperation, TypeError) as error:
        raise ValueError('Exact decimal compiler timeout required') from error
    # A fractional nanosecond cannot cause expiry before the configured limit.
    return (numerator * 1_000_000_000 + denominator - 1) // denominator


class CompilerTimeout(TimeoutError):
    pass


class CompilerDeadline:
    def __init__(self, timeout_ns):
        if not isinstance(timeout_ns, int) or timeout_ns <= 0:
            raise ValueError('Positive integer compiler nanoseconds required')
        self.started_ns = time.monotonic_ns()
        self.timeout_ns = timeout_ns
        self.deadline_ns = self.started_ns + timeout_ns

    def remaining_ns(self):
        remaining = self.deadline_ns - time.monotonic_ns()
        if remaining <= 0:
            raise CompilerTimeout('Actual compilation deadline reached')
        return remaining

    def wait(self, process):
        try:
            while True:
                wait_ns = min(self.remaining_ns(), WAIT_NS)
                try:
                    output = process.communicate(timeout=wait_ns / 1_000_000_000)
                except subprocess.TimeoutExpired:
                    continue
                self.remaining_ns()
                return output
        except BaseException:
            if process.poll() is None:
                process.kill()
            process.communicate()
            raise
