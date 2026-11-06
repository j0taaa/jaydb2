#!/usr/bin/env python3
"""Reject false arithmetic, comparisons, public-decoder and read-only proofs."""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.bend import executable, environment


def main():
    for fixture in sorted((ROOT / 'experiments/library/rejected').glob('*.bend')):
        for mode in ('--check-only', '--verdict'):
            result = subprocess.run([str(executable()), str(fixture), mode], env=environment(),
                                    capture_output=True, text=True, timeout=120)
            output = result.stdout + result.stderr
            assert result.returncode and 'SOME PROOFS FAIL' in output, output
            assert 'Location: bad_' in output and '- expected :' in output and '- observed :' in output, output
            assert 'a defined name' not in output and 'a filled definition' not in output, output
            print(f'PASS rejected {fixture.name} {mode}')


if __name__ == '__main__':
    main()
