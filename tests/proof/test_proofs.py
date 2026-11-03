#!/usr/bin/env python3
"""Causal negative controls; `make verify` checks the positive aggregates."""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.bend import environment, executable


def main():
    # Each mutation removes a different premise: bytes, administrative law,
    # publishable state, authentication, construction guard, or reification.
    compiler = executable()
    for path in sorted(Path(__file__).with_name('rejected').glob('*.bend')):
        run = subprocess.run([str(compiler), str(path), '--check-only'],
            cwd=ROOT, env=environment(), capture_output=True, text=True, timeout=600)
        output = run.stdout + run.stderr
        if not (run.returncode and 'SOME PROOFS FAIL' in output
                and 'Location: false' in output and '- expected :' in output
                and '- observed :' in output and 'a defined name' not in output):
            raise AssertionError(f'Expected a false proof, not a broken fixture: {path}\n{output}')
        print(f'OK rejected: {path.relative_to(ROOT)}', flush=True)


if __name__ == '__main__':
    main()
