#!/usr/bin/env python3
"""Check executable contract witnesses with the pinned official tools."""
import argparse
import hashlib
import json
import shutil
from pathlib import Path
import subprocess
import sys


sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from bend import environment, executable, verify_version


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bend", help="Pinned official Bend 2.0.39 executable")
    parser.add_argument("--verdict", action="store_true", help="Also run the official BendTT verdict")
    parser.add_argument("--report", default="VERIFICATION.json")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    compiler = verify_version(Path(shutil.which(args.bend) or args.bend).resolve()) if args.bend else executable()
    env = environment()
    version = subprocess.run([str(compiler), "version"], cwd=root, env=env,
                             capture_output=True, text=True, check=False)
    checks = []
    for mode in ["--check-only"] + (["--verdict"] if args.verdict else []):
        result = subprocess.run([str(compiler), str(root / "VERIFY.bend"), mode],
                                cwd=root, env=env, capture_output=True, text=True, check=False)
        checks.append({"command": ["bend", "VERIFY.bend", mode], "exit_code": result.returncode,
                       "stdout": result.stdout, "stderr": result.stderr})
    exit_code = next((c["exit_code"] or 1 for c in checks
                      if c["exit_code"] or "ALL PROOFS CHECK" not in c["stdout"]), 0)
    stdout = "".join(c["stdout"] for c in checks)
    stderr = "".join(c["stderr"] for c in checks)
    sources = sorted(root.glob("*.bend"))
    report = {
        "bend_version": version.stdout.strip(),
        "checks": checks,
        "exit_code": exit_code,
        "stdout": stdout,
        "stderr": stderr,
        "secondary_kernel_requested": args.verdict,
        "native_implementation_included": False,
        "native_contract_proved": False,
        "scope": "Statement/definition types; included lemmas and closed examples; inhabited executed Startup/recovery, abstract Init, prepared Control, mixed ServiceFold, all four Core clauses, ordinary/prepared ingress, the finite-run fold and independent wire theorems.",
        "executable_witnesses": ["Configuration.startup_theorem", "Init.init_theorem", "ControlClauses.control_theorem", "ControlHistory.service_fold_theorem", "ControlHistory.service_lifetime_theorem", "ControlHistory.service_no_revival_theorem", "ControlHistory.registry_lookup_theorem", "ControlHistory.registry_invalidation_theorem", "CoreClauses.core_theorem", "Ingress.ingress_theorem", "Ingress.unified_core_theorem", "Iteration.fold_theorem", "WireTheorems.codec_roundtrip",
                                 "WireTheorems.codec_canonical", "WireTheorems.framing_roundtrip"],
        "pending_theorems": [],
        "sources": [{"file": p.name, "sha256": hashlib.sha256(p.read_bytes()).hexdigest(),
                     "lines": len(p.read_text().splitlines())} for p in sources],
    }
    (root / args.report).write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    sys.stdout.write(stdout)
    sys.stderr.write(stderr)
    print("Scope: inhabited Startup/Init/Core/Ingress/UnifiedCore/Fold/Control/ServiceFold/wire theorems; native worker executes Gate under T2/T3.")
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
