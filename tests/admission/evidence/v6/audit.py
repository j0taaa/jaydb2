#!/usr/bin/env python3
"""Read-only V6 pin/source/history audit. Run from a prepared checkout."""
import hashlib
import json
from pathlib import Path
import sys

root = Path(__file__).resolve().parents[4]
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
report = {}

def check_group(name, entries):
    results = {str(p.relative_to(root)): {"expected": expected, "actual": digest(p)}
               for p, expected in entries}
    report[name] = {"files": len(results), "mismatches": [p for p, v in results.items() if v["expected"] != v["actual"]], "sha256": results}

for manifest, prefix in [("contrato-original.sha256.json", "history/contrato-v1"), ("contrato.sha256.json", "")]:
    pins = json.loads((root / manifest).read_text())
    check_group(manifest, [(root / prefix / p, h) for p, h in pins.items()])

pins = json.loads((root / "tools/admission/toolchain.lock.json").read_text())
check_group("officialSources", [(root / (".tools/bend-source-" + pins["version"]) / p, h) for p, h in pins["files"].items()])
check_group("originalExecutables", [(root / (".tools/bendtt-" + pins["kernelSha256"]), pins["kernelSha256"]), (root / (".tools/bend-" + pins["version"]) / "bin/bend", pins["officialBinarySha256"])])
frontend = json.loads((root / "tools/admission/frontend.lock.json").read_text())
check_group("installedFrontend", [(root / "tools/admission/installed" / p, h) for p, h in frontend["files"].items()])
check_group("frontendTransforms", [(root / "tools/admission" / p, h) for p, h in frontend["transforms"].items()])
check_group("frontendManifest", [(root / "tools/admission/installed/manifest.json", digest(root / "tools/admission/frontend.lock.json"))])
check_group("nativeGeneric", [(root / "tools/native/generic.mjs", "4b71ed5150db96dd46a87ceeaf91819ba0e42b571818f98698eddc6319037ac3")])
fixture_pins = json.loads((root / "tests/admission/cases/v6/literal-v5.json").read_text())
check_group("literalV5Fixtures", [(root / "tests/admission/cases/v6" / p, h) for p, h in fixture_pins.items()])
historical = {
    "resources_v1.tar.gz": "e4aad606cc9797befd4dae44ea09cca7d4afb763d27e6063fb5d246a0cb348c1",
    "resources_v2.tar.gz": "bb9280e33ec0c71a10f9e232c998ac798e272d5d4829a396af4c29b5de959e6b",
    "resources_v3.tar.gz": "80ea97ee473afad0ea47dbed707d5b292c775b9e4a60dc7ebca2bd1b7d19746f",
    "resources_v4.tar.gz": "86fc99d699d272f1236fc6af51c488695e6dab53c242eea8fb00c56a9f090079",
    "resources_v5.tar.gz": "5b25af281096b44c682559c83c56d49a89c90b41ad964d1b30a0749531de5bba",
    "review_v5_literal.tar.gz": "1afcd9fbdec1cec348aa3cc650b1917e3ff7f2a6dfd83d24401c472a7fc0f69f",
}
check_group("historicalArchives", [(root / "tests/admission/checkpoints" / p, h) for p, h in historical.items()])
report["status"] = "PASS" if all(not v["mismatches"] for v in report.values()) else "FAIL"
text = json.dumps(report, indent=2) + "\n"
if len(sys.argv) > 1:
    Path(sys.argv[1]).write_text(text)
else:
    print(text, end="")
sys.exit(0 if report["status"] == "PASS" else 1)
