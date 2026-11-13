#!/usr/bin/env python3
"""Capture actual RLS negative controls and render a literal rejection excerpt.

Run from the repository root under the documented heavy-work lock:
flock /tmp/jaydb2-experiments-heavy.lock bash -c \
  'ulimit -s unlimited; python3 -B paper/presentation/capture_checker_figures.py'
The existing test helpers assert the failure location in both official modes.
"""
from html import escape
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
ASSETS = Path(__file__).resolve().parent / 'assets'
sys.path[:0] = [str(ROOT), str(ROOT / 'applications/rls')]
from check import BUILD, proof_root
from negative_cases import cases, rejected


def main():
    for name, code, proof, expected, context in cases():
        if name not in ('read-bob', 'create-without-directory'):
            continue
        rejected(name, proof_root(name, code, proof, context=context), expected)
        for mode in ('check-only', 'verdict'):
            filename = f'{name}-{mode}.txt'
            (ASSETS / filename).write_bytes((BUILD / f'{name}-{mode}.log').read_bytes())
    raw = (ASSETS / 'read-bob-check-only.txt').read_text()
    # Literal first five diagnostic lines; ellipsis marks the omitted context.
    lines = raw.splitlines()[:5] + ['…']
    body = ''.join(f'<text x="32" y="{122 + i * 48}">{escape(line)}</text>'
                   for i, line in enumerate(lines))
    (ASSETS / 'checker-rejection.svg').write_text(
        '<svg xmlns="http://www.w3.org/2000/svg" width="620" height="432" '
        'viewBox="0 0 620 432" role="img">'
        '<title>Literal Bend rejection: read-bob --check-only</title>'
        '<rect width="620" height="432" rx="8" fill="#102f3b"/>'
        '<text x="32" y="46" fill="#b4e6c8" font-family="monospace" '
        'font-size="25">Bend --check-only · read-bob</text>'
        '<path d="M32 70H588" stroke="#637574"/>'
        f'<g fill="#f4f1e8" font-family="monospace" font-size="32">{body}</g>'
        '</svg>\n')


if __name__ == '__main__':
    main()
