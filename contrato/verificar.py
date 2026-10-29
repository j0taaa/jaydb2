#!/usr/bin/env python3
"""Verifica o pacote sem executar um servidor e sem alegar prova do nucleo."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bend", default="bend", help="Executavel do Bend 2.0.39")
    parser.add_argument("--verdict", action="store_true", help="Pedir tambem o kernel BendTT")
    parser.add_argument("--relatorio", default="VERIFICACAO.json")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    env = os.environ.copy()
    env["BEND_NO_TELEMETRY"] = "1"
    version = subprocess.run([args.bend, "version"], cwd=root, env=env,
                             capture_output=True, text=True, check=False)
    command = [args.bend, str(root / "VERIFICAR.bend"), "--check-only"]
    if args.verdict:
        command.append("--verdict")
    checked = subprocess.run(command, cwd=root, env=env, capture_output=True,
                             text=True, check=False)
    sources = sorted(root.glob("*.bend"))
    report = {
        "bend_version": version.stdout.strip(),
        "command": ["bend", "VERIFICAR.bend", "--check-only"] + (["--verdict"] if args.verdict else []),
        "exit_code": checked.returncode,
        "stdout": checked.stdout,
        "stderr": checked.stderr,
        "secondary_kernel_requested": args.verdict,
        "native_implementation_included": False,
        "native_contract_proved": False,
        "scope": "Tipos dos enunciados/definicoes; provas dos lemas incluidos; exemplos fechados.",
        "sources": [{"file": p.name, "sha256": hashlib.sha256(p.read_bytes()).hexdigest(),
                     "lines": len(p.read_text().splitlines())} for p in sources],
    }
    (root / args.relatorio).write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    sys.stdout.write(checked.stdout)
    sys.stderr.write(checked.stderr)
    print("Escopo: especificacao e lemas; a prova de Contrato(a,k) para um nucleo nativo nao esta incluida.")
    return checked.returncode


if __name__ == "__main__":
    raise SystemExit(main())
