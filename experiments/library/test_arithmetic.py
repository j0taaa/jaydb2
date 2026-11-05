#!/usr/bin/env python3
"""Compare the literal official native C to Python signed64 arithmetic."""
from pathlib import Path
import hashlib
import random
import resource
import struct
import subprocess

ROOT = Path(__file__).resolve().parents[2]
BUILD = ROOT / 'build/library'
MIN, MAX = -(1 << 63), (1 << 63) - 1


def main():
    BUILD.mkdir(parents=True, exist_ok=True)
    _, hard = resource.getrlimit(resource.RLIMIT_STACK)
    resource.setrlimit(resource.RLIMIT_STACK, (hard, hard))
    source, binary = BUILD / 'arithmetic.c', BUILD / 'arithmetic'
    subprocess.run(['node', '--stack_size=65536', str(ROOT / 'tests/native/emit_fixture.mjs'),
                    str(ROOT / '.tools/bend-source-2.0.39/bend2'),
                    str(ROOT / 'experiments/library/ArithmeticRuntime.bend'), str(source)], check=True, timeout=120)
    digest = hashlib.sha256(source.read_bytes()).digest()
    subprocess.run(['/usr/bin/clang-19', '-std=gnu11', '-O2', '-w', '--no-default-config', str(source),
                    '-o', str(binary), '-lm', '-pthread'], check=True, timeout=120)
    assert hashlib.sha256(source.read_bytes()).digest() == digest
    boundary = [MIN, MIN + 1, -(1 << 48), -(1 << 32), -2, -1, 0, 1, 2,
                (1 << 32) - 1, 1 << 32, (1 << 48) + 1, MAX - 1, MAX]
    pairs = [(a, b) for a in boundary for b in boundary]
    rng = random.Random(5925)
    pairs += [(rng.randrange(MIN, MAX + 1), rng.randrange(MIN, MAX + 1)) for _ in range(100)]
    pairs += [(rng.randrange(MIN, MAX + 1), rng.randrange(-3, 4)) for _ in range(100)]
    incoming, expected = bytearray(), bytearray()
    for op in range(10):
        for a, b in pairs:
            incoming += bytes([op]) + struct.pack('<qq', a, b)
            if op == 5:
                expected += b'\1' + struct.pack('<qq', min(a, b), max(a, b))
                continue
            if op == 6:
                total = a + b
                if MIN <= total <= MAX:
                    expected += b'\1' + struct.pack('<q', (abs(total) // 2) * (-1 if total < 0 else 1))
                else:
                    expected += b'\0'
                continue
            if op == 7:
                total = a + b
                expected += b'\1' + struct.pack('<qq', 2, total) if MIN <= total <= MAX else b'\0'
                continue
            if op == 8:
                expected += bytes([2 if a == b else 1])
                continue
            if op == 9:
                expected += bytes([1 if a == b else 2])
                continue
            if op == 4:
                expected += bytes([a < b])
                continue
            if op == 3:
                if not b or (a == MIN and b == -1):
                    expected += b'\0'
                else:
                    q = (abs(a) // abs(b)) * (-1 if (a < 0) != (b < 0) else 1)
                    expected += b'\1' + struct.pack('<qq', q, a - q * b)
            else:
                n = (a + b, a - b, a * b)[op]
                expected += b'\1' + struct.pack('<q', n) if MIN <= n <= MAX else b'\0'
    actual = subprocess.run([str(binary), '+RTS', '--threads', '1', '--gpu', 'off', '-RTS'],
                            input=incoming, capture_output=True, check=True, timeout=120).stdout
    assert actual == expected, (len(actual), len(expected), next((i for i, p in enumerate(zip(actual, expected)) if p[0] != p[1]), None))
    print(f'PASS: {len(pairs) * 5} native dynamic signed64 add/sub/mul/divmod/order cases and {len(pairs) * 5} sort/average/summary/join/group cases; official C unchanged.')


if __name__ == '__main__':
    main()
