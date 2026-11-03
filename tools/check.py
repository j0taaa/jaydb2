#!/usr/bin/env python3
"""Check the historical snapshot, active contract and both Bend checkers."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

from bend import ROOT, environment, executable


def check_originals() -> None:
    manifest = json.loads((ROOT / "contract-original.sha256.json").read_text())
    for relative, expected in manifest.items():
        path = ROOT / "history" / "contract-v1" / relative
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise RuntimeError(f"Historical contract snapshot changed: {relative}")


def check_active() -> None:
    manifest = json.loads((ROOT / "contract.sha256.json").read_text())
    for relative, expected in manifest.items():
        path = ROOT / relative
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise RuntimeError(f"Active contract differs from its manifest: {relative}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout", type=int, default=600,
                        help="Seconds per checker for development verification")
    parser.add_argument("files", type=Path, nargs="*")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    check_originals()
    check_active()
    compiler = executable()
    files = args.files or [ROOT / "contract" / "VERIFY.bend"]
    for file in files:
        path = file.resolve()
        for option in ("--check-only", "--verdict"):
            result = subprocess.run(
                [str(compiler), str(path), option], env=environment(),
                capture_output=True, text=True, timeout=args.timeout,
            )
            if result.returncode or "ALL PROOFS CHECK" not in result.stdout:
                sys.stdout.write(result.stdout)
                sys.stderr.write(result.stderr)
                return result.returncode or 1
            print(f"OK {option}: {path.relative_to(ROOT)}", flush=True)
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, subprocess.SubprocessError) as error:
        print(str(error), file=sys.stderr)
        raise SystemExit(1)
