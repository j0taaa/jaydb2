#!/usr/bin/env python3
"""Check the active contract and both Bend checkers."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

from bend import ROOT, environment, executable


def check_active() -> None:
    manifest = json.loads((ROOT / "contract.sha256.json").read_text())
    for relative, expected in manifest.items():
        path = ROOT / relative
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise RuntimeError(f"Active contract differs from its manifest: {relative}")


COVERAGE_AREAS = ("contract", "src", "proof", "library")


def check_coverage(files: list[Path], root: Path = ROOT) -> dict:
    """Check maintained import coverage, not the semantic content of proofs.

    This deliberately recognizes only the repository's local header syntax.
    The official tools still parse and check every declaration afterwards.
    Reject unknown imports rather than silently omitting an edge.
    """
    root = root.resolve()
    seen: dict[Path, dict] = {}
    specifier = r"(?:\./)?(?:\.\./)*(?:[A-Za-z_][\w-]*/)*[A-Za-z_][\w-]*\.bend"
    local = re.compile(r"import\s+(" + specifier + r")\s+as\s+[A-Za-z_]\w*\s*(?:#.*)?$")

    def visit(file: Path) -> None:
        file = file.resolve()
        if not file.is_relative_to(root):
            raise RuntimeError(f"Verification import escapes the repository: {file}")
        if file in seen:
            return
        if not file.is_file():
            raise RuntimeError(f"Missing verification module: {file.relative_to(root)}")
        raw = file.read_bytes()
        source = raw.decode("utf-8")
        seen[file] = {"path": str(file.relative_to(root)),
                      "sha256": hashlib.sha256(raw).hexdigest(),
                      "law_declarations": len(re.findall(r"^law\s+", source, re.MULTILINE))}
        for line in source.split("\n"):
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            if not re.match(r"import(?:\s|$)", line):
                break
            if re.fullmatch(r"import\s+Base\s*(?:#.*)?", line):
                continue
            match = local.fullmatch(line)
            if match is None:
                raise RuntimeError(f"Unsupported verification import in {file.relative_to(root)}: {line}")
            visit(file.parent / match.group(1))

    for file in files:
        visit(file)
    areas = {}
    for area in COVERAGE_AREAS:
        expected = {file.resolve() for file in (root / area).rglob("*.bend")}
        missing = sorted(str(file.relative_to(root)) for file in expected - seen.keys())
        if missing:
            raise RuntimeError("Bend modules outside verification roots: " + ", ".join(missing))
        areas[area] = {"modules": len(expected),
                       "law_declarations": sum(seen[file]["law_declarations"] for file in expected)}
    return {"scope": "Import coverage of maintained Bend modules; not a proof of every functional specification or host refinement.",
            "roots": [str(file.resolve().relative_to(root)) for file in files],
            "areas": areas,
            "modules": sorted(seen.values(), key=lambda item: item["path"])}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout", type=int, default=600,
                        help="Seconds per checker for development verification")
    parser.add_argument("--coverage", action="store_true",
                        help="Require the selected roots to import every contract/src/proof/library Bend module")
    parser.add_argument("files", type=Path, nargs="*")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    check_active()
    files = args.files or [ROOT / "contract" / "VERIFY.bend"]
    if args.coverage:
        report = check_coverage(files)
        print("OK import coverage: " + ", ".join(
            f"{area} {counts['modules']} modules" for area, counts in report["areas"].items()), flush=True)
    compiler = executable()
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
