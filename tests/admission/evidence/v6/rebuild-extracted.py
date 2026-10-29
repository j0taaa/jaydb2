#!/usr/bin/env python3
"""Extract the owned V6 snapshot and rebuild using pinned local prerequisites.

Usage: rebuild-extracted.py ARCHIVE DESTINATION PREPARED_CHECKOUT REPORT
Writes only DESTINATION and REPORT; never rebuilds the prepared checkout.
The original Bend package, Lean 4.34, Node24 and clang19 must exist locally.
"""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile

archive, destination, prepared, report_path = map(lambda p: Path(p).resolve(), sys.argv[1:])
if destination.exists():
    raise SystemExit("Destination must not exist")
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
destination.mkdir(parents=True)
with tarfile.open(archive) as tar:
    tar.extractall(destination, filter="data")

def copy(relative, expected=None):
    source, target = prepared / relative, destination / relative
    if expected is not None:
        assert digest(source) == expected, relative
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, target)

lock = json.loads((destination / "tools/admission/toolchain.lock.json").read_text())
for name, expected in lock["files"].items():
    copy(".tools/bend-source-" + lock["version"] + "/" + name, expected)
copy(".tools/bendtt-" + lock["kernelSha256"], lock["kernelSha256"])
copy(".tools/bend-" + lock["version"] + "/bin/bend", lock["officialBinarySha256"])
for name in ["base.bend", "bendtt.lean"]:
    copy(".tools/bend-" + lock["version"] + "/bend2/" + name, lock["files"]["bend2/" + name])
copy("tools/native/generic.mjs", "4b71ed5150db96dd46a87ceeaf91819ba0e42b571818f98698eddc6319037ac3")
for manifest, prefix in [("contrato.sha256.json", ""), ("contrato-original.sha256.json", "history/contrato-v1/")]:
    copy(manifest)
    for name, expected in json.loads((destination / manifest).read_text()).items():
        copy(prefix + name, expected)
for name in ["resources_v1", "resources_v2", "resources_v3", "resources_v4", "resources_v5", "review_v5_literal"]:
    copy("tests/admission/checkpoints/" + name + ".tar.gz")

logs = report_path.parent / (report_path.stem + "-logs")
logs.mkdir(parents=True, exist_ok=True)
def run(name, args):
    result = subprocess.run(args, cwd=destination, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (logs / (name + ".log")).write_bytes(result.stdout)
    assert result.returncode == 0, name + ": " + result.stdout.decode(errors="replace")[-4000:]

frontend_path = destination / "tools/admission/installed"
frontend_pin = json.loads((destination / "tools/admission/frontend.lock.json").read_text())
manifest_bytes = (frontend_path / "manifest.json").read_bytes()
addon_bytes = (frontend_path / "stack.node").read_bytes()
run("frontend-build", ["node", "tools/admission/build-frontend.mjs"])
frontend_files = {name: {"expected": expected, "rebuilt": digest(frontend_path / name)} for name, expected in frontend_pin["files"].items()}
assert all(v["expected"] == v["rebuilt"] for name, v in frontend_files.items() if name != "stack.node")
# __FILE__ in NODE_MODULE_INIT metadata records the build directory. Restore
# the authenticated addon before API tests; do not accept an unpinned addon.
(frontend_path / "stack.node").write_bytes(addon_bytes)
(frontend_path / "manifest.json").write_bytes(manifest_bytes)

run("verifier-build", ["node", "tools/verifier/build.mjs"])
verifier = json.loads((destination / "tools/verifier/verifier.lock.json").read_text())
verifier_dir = destination / (".tools/build/verifier-" + verifier["sourceSha256"])
assert (verifier_dir / "manifest.json").read_bytes() == (destination / "tools/verifier/verifier.lock.json").read_bytes()
assert digest(verifier_dir / "bendtt-budget") == verifier["kernelSha256"]
run("source-audit", ["python3", "tests/admission/evidence/v6/audit.py", str(logs / "source-audit.json")])
run("api-r4-r5", ["node", "--test", "--test-concurrency=1", "--test-name-pattern=intern_self_minimal|ordinary_reflexive_boundary", "tests/admission/structural.test.mjs"])
report = {"status": "PASS", "archiveSha256": digest(archive), "destination": str(destination), "preparedPrerequisites": str(prepared),
          "frontendFiles": frontend_files, "javascriptIdentical": True,
          "nativeAddon": "absolute __FILE__ metadata differs by directory; original pinned addon restored before API checks",
          "verifierManifestAndBinaryIdentical": True, "verifierKernelSha256": verifier["kernelSha256"],
          "apiSmoke": {"pass": 2, "fail": 0, "cases": ["R4 intern_self_minimal", "R5 ordinary_reflexive_boundary"]},
          "logs": {p.name: digest(p) for p in sorted(logs.iterdir()) if p.is_file()}}
report_path.write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({"status": report["status"], "archiveSha256": report["archiveSha256"], "report": str(report_path)}))
