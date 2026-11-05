#!/usr/bin/env python3
"""Independent content/stability oracle for variable-length native records."""
from pathlib import Path
import hashlib
import random
import resource
import struct
import subprocess

ROOT = Path(__file__).resolve().parents[2]
BUILD = ROOT / 'build/library'


def packed(items):
    return struct.pack('<H', len(items)) + bytes(v for item in items for v in item)


def main():
    BUILD.mkdir(parents=True, exist_ok=True)
    _, hard = resource.getrlimit(resource.RLIMIT_STACK)
    resource.setrlimit(resource.RLIMIT_STACK, (hard, hard))
    source, binary = BUILD / 'collections.c', BUILD / 'collections'
    subprocess.run(['node', '--stack_size=65536', str(ROOT / 'tests/native/emit_fixture.mjs'),
                    str(ROOT / '.tools/bend-source-2.0.39/bend2'),
                    str(ROOT / 'experiments/library/CollectionRuntime.bend'), str(source)], check=True, timeout=120)
    digest = hashlib.sha256(source.read_bytes()).digest()
    subprocess.run(['/usr/bin/clang-19', '-std=gnu11', '-O2', '-w', '--no-default-config', str(source),
                    '-o', str(binary), '-lm', '-pthread'], check=True, timeout=120)
    assert hashlib.sha256(source.read_bytes()).digest() == digest
    rng = random.Random(20261105)
    cases = [([], []), ([1], []), ([2, 2, 2, 2], [2, 2]),
             ([3, 1, 3, 0, 1, 3, 0], [3, 1, 1, 7]),
             (list(range(7, -1, -1)), list(range(8))),
             ([1] * 40, [1] * 12)]
    cases += [([rng.randrange(8) for _ in range(n)],
               [rng.randrange(8) for _ in range(rng.randrange(25))])
              for n in [0, 1, 2, 3, 4, 8, 16, 31, 48, 64, 80] for _ in range(4)]
    for ci, (lk, rk) in enumerate(cases):
        left = [(k, i) for i, k in enumerate(lk)]
        right = [(k, 128 + i) for i, k in enumerate(rk)]
        joins = [(a[0], a[1], b[0], b[1]) for a in left for b in right if a[0] == b[0]]
        outer = []
        for a in left:
            found = [b for b in right if a[0] == b[0]]
            outer += [(a[0], a[1], b[0], b[1]) for b in found] if found else [(a[0], a[1], 255, 255)]
        # Independent grouping: group order is descending last position;
        # members are selected in original order, with original identities.
        keys = sorted(set(lk), key=lambda k: max(i for i, x in enumerate(lk) if x == k), reverse=True)
        groups = struct.pack('<H', len(keys))
        for k in keys:
            groups += bytes([k]) + packed([x for x in left if x[0] == k])
        expected = [packed(sorted(left, key=lambda x: x[0])),
                    packed(sorted(left, key=lambda x: x[0] % 2)),
                    packed(joins), packed(outer), groups]
        for op, want in enumerate(expected):
            incoming = bytes([op, len(left), len(right)]) + bytes(x for p in left + right for x in p)
            actual = subprocess.run([str(binary), '+RTS', '--threads', '1', '--gpu', 'off', '-RTS'],
                                    input=incoming, capture_output=True, check=True, timeout=30).stdout
            assert actual == want, (ci, op, left, right, actual, want)
    print(f'PASS: {len(cases)*5} variable-length native content cases (lengths 0..80); duplicates, stable equal-key identities, complete inner/left join pairs and group keys/members; official C unchanged.')


if __name__ == '__main__':
    main()
