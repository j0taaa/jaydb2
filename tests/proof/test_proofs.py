#!/usr/bin/env python3
"""Verifica provas gerais, instancia positiva e mutacoes que devem falhar."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.bend import executable

HERE = Path(__file__).resolve().parent
POSITIVES = [ROOT / "proof/VERIFICAR.bend", HERE / "VERIFICAR.bend"]
MODES = ("--check-only", "--verdict")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def contract_originals() -> dict[str, str]:
    preserved = ROOT / "history/contrato-v1"
    originals = json.loads((preserved / "contrato-original.sha256.json").read_text())
    for relative, expected in originals.items():
        if digest(preserved / relative) != expected:
            raise AssertionError(f"Historico do contrato original alterado: {relative}")
    return originals


def contract_active() -> dict[str, str]:
    active = json.loads((ROOT / "contrato.sha256.json").read_text())
    for relative, expected in active.items():
        if digest(ROOT / relative) != expected:
            raise AssertionError(f"Contrato ativo diverge do manifesto: {relative}")
    return active


def dependencies(entries: list[Path]) -> dict[str, str]:
    found: dict[str, str] = {}
    pending = list(entries)
    while pending:
        path = pending.pop().resolve()
        relative = str(path.relative_to(ROOT))
        if relative in found:
            continue
        found[relative] = digest(path)
        for imported in re.findall(r"^import\s+(\.{1,2}/[^\s]+\.bend)\s+as\s+", path.read_text(), re.M):
            pending.append(path.parent / imported)
    return dict(sorted(found.items()))


def source_guards() -> None:
    # Guarda de regressao limitada; os checkers, e nao este scan, provam termos.
    for path in sorted((ROOT / "proof").glob("*.bend")):
        source = "\n".join(line.split("#", 1)[0] for line in path.read_text().splitlines())
        forbidden = (
            r"@unsafe", r"\bdef\s+[\w.]+\?", r"\?[A-Za-z_]",
            r'^import\s+["\']', r"\b(?:I\.)?Ambiente\s*\{",
            r"\bfor\s+[^:\n]+:\s*(?:\w+\.)?(?:Contrato|Lei[1-8])\s*\(",
        )
        for pattern in forbidden:
            if re.search(pattern, source, re.M):
                raise AssertionError(f"Premissa proibida, meta, efeito ou ambiente artificial: {path.name}")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bend", type=Path, help="Distribuição Bend; padrão local fixado ou JAYDB_BEND")
    parser.add_argument("--timeout", type=int, default=600, help="Segundos por checker")
    parser.add_argument("--record", action="store_true", help="Grava RESULTADOS_RECURSOS_SIMPLES.json")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout deve ser positivo")
    compiler = args.bend.resolve() if args.bend else executable()
    env = dict(os.environ, BEND_NO_TELEMETRY="1")
    version = subprocess.run([str(compiler), "version"], env=env, capture_output=True, text=True, check=True, timeout=15).stdout.strip()
    if version != "bend 2.0.39":
        raise AssertionError(f"Exigido Bend 2.0.39, recebido {version!r}")
    originals = contract_originals()
    active = contract_active()
    source_guards()
    negatives = sorted([*(HERE / "rejeitados").glob("*.bend"),
                        *HERE.glob("EntradaRejeita*.bend")])
    entries = POSITIVES + negatives
    source_hashes = dependencies(entries)
    results: list[dict[str, object]] = []
    started = time.monotonic()
    for path in entries:
        rejection = path in negatives
        for mode in MODES:
            run = subprocess.run([str(compiler), str(path), mode], cwd=ROOT, env=env,
                                 capture_output=True, text=True, timeout=args.timeout)
            output = run.stdout + run.stderr
            if rejection:
                correct = (run.returncode != 0 and "SOME PROOFS FAIL" in output
                           and "Location: falso" in output and "- expected :" in output
                           and "- observed :" in output and "a defined name" not in output)
            else:
                correct = run.returncode == 0 and "ALL PROOFS CHECK" in output
            if not correct:
                raise AssertionError(f"Resultado inesperado: {path.relative_to(ROOT)} {mode}\n{output}")
            results.append({"file": str(path.relative_to(ROOT)), "mode": mode,
                            "expected": "rejected" if rejection else "accepted", "exitCode": run.returncode,
                            "output": output})
            print(f"OK {mode} {'REJEITADO' if rejection else 'ACEITO'}: {path.relative_to(ROOT)}", flush=True)
    if source_hashes != dependencies(entries):
        raise AssertionError("Dependencias mudaram durante a verificacao; execute novamente.")
    contract_originals()
    if contract_active() != active:
        raise AssertionError("Manifesto do contrato ativo mudou durante a verificacao")
    report = {
        "checkedAt": datetime.now(timezone.utc).isoformat(),
        "compiler": str(compiler), "version": version, "compilerSha256": digest(compiler),
        "kernelSha256": digest(Path(env["BENDTT"])) if env.get("BENDTT") else None,
        "durationSeconds": round(time.monotonic() - started, 3),
        "contractRevision": "tres-tamanhos-sem-orcamentos-fisicos-v2",
        "harnessTimeoutIsDevelopmentOnly": True,
        "physicalProofsArchive": "history/provas-recursos-v1",
        "fullExecutableContractProved": False,
        "acceptedAggregates": len(POSITIVES), "rejectedMutations": len(negatives),
        "checks": results, "dependenciesSha256": source_hashes, "originalsSha256": originals,
        "activeContractSha256": active,
    }
    if args.record:
        (HERE / "RESULTADOS_RECURSOS_SIMPLES.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print(f"{len(results)} verificacoes OK; historico original integro; contrato revisado verificado.", flush=True)


if __name__ == "__main__":
    main()
