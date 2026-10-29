#!/usr/bin/env python3
"""Verifica contrato, wrappers e certificados dos exemplos com tres limites."""
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
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.bend import executable

HERE = Path(__file__).resolve().parent
MODES = ("--check-only", "--verdict")
CASES = (
    ("sem-observacoes", "Client", "ClientProof"),
    ("sem-observacoes", "Sucesso", "SucessoProof"),
    ("credenciais", "Client", "ClientProof"),
    ("credenciais", "Eco", "EcoProof"),
    ("troca-credenciais", "Client", "ClientProof"),
    ("troca-credenciais", "Quem", "QuemProof"),
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sources() -> dict[str, str]:
    paths = [*ROOT.glob("contrato/*.bend"), *ROOT.glob("src/*.bend"),
             *ROOT.glob("examples/**/*.bend"),
             HERE / "NucleoVerificar.bend", Path(__file__).resolve()]
    return {str(p.relative_to(ROOT)): digest(p) for p in sorted(paths)}


def literal(source: str) -> str:
    return '"' + ''.join('\\"' if c == '"' else '\\\\' if c == '\\'
                         else f'\\u{{{ord(c):02x}}}' if ord(c) < 32 else c
                         for c in source) + '"'


def stage(folder: Path, example: str, program: str, proof: str) -> dict[str, str]:
    # Only imports of repository-owned modules are relocated; example sources
    # and proofs are copied literally, as in the host's flat public workspace.
    for source in [*ROOT.glob("contrato/*.bend"), *ROOT.glob("src/*.bend")]:
        text = re.sub(r"(?m)^(import\s+)(?:\.{1,2}/)+(?:[^\s/]+/)*([^/\s]+\.bend)(\s+as\s+)",
                      r"\1./\2\3", source.read_text())
        (folder / source.name).write_text(text)
    source = ROOT / "examples" / example
    for name in ("Configuration", "Seed"):
        (folder / f"{name}.bend").write_bytes((source / f"{name}.bend").read_bytes())
    code = (source / f"{program}.bend").read_text()
    (folder / "Client.bend").write_bytes((source / f"{program}.bend").read_bytes())
    (folder / "ClientProof.bend").write_bytes((source / f"{proof}.bend").read_bytes())
    generated = {
        "Environment.bend": 'import Base\ndef identidade() -> String:\n  "Bend-2.0.39-tres-limites-testes"\n',
        "Instance.bend": '''import Base
import ./Dados.bend as D
import ./Semantica.bend as S
import ./Configuration.bend as C
def config() -> S.Configuracao:
  C.config()
def contexto() -> D.Contexto:
  D.Contexto{"alice", "usuario"}
def argumentos() -> D.Valor:
  D.VAusente{}
''',
        "Bindings.bend": '''import Base
import ./Dados.bend as D
import ./Semantica.bend as S
import ./Requisitos.bend as R
import ./Interface.bend as F
import ./Instance.bend as I
import ./Client.bend as Client
def codigo() -> String:
  CODE
law certificado:
  R.Certifica(I.config(), codigo(), Client.programa(), I.contexto(), I.argumentos())
law termina:
  F.ProgramaTermina(I.config(), Client.programa())
'''.replace("CODE", literal(code)),
        "Verificar.bend": '''import Base
import ./Configuration.bend as Configuration
import ./Seed.bend as Seed
import ./ClientProof.bend as ClientProof
''',
    }
    for name, text in generated.items():
        (folder / name).write_text(text)
    return generated


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bend", type=Path)
    parser.add_argument("--timeout", type=int, default=600, help="Segundos por checker; apenas desenvolvimento")
    parser.add_argument("--record", action="store_true")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout deve ser positivo")
    compiler = args.bend.resolve() if args.bend else executable()
    env = dict(os.environ, BEND_NO_TELEMETRY="1")
    version = subprocess.run([str(compiler), "version"], env=env, capture_output=True,
                             text=True, check=True, timeout=15).stdout.strip()
    if version != "bend 2.0.39":
        raise AssertionError(f"Distribuicao exigida: Bend 2.0.39; recebido {version!r}")
    source_hashes = sources()
    checks = []
    generated_cases = {}
    started = time.monotonic()

    def check(path: Path, label: str) -> None:
        for mode in MODES:
            run = subprocess.run([str(compiler), str(path), mode], cwd=ROOT, env=env,
                                 capture_output=True, text=True, timeout=args.timeout)
            output = run.stdout + run.stderr
            if run.returncode or "ALL PROOFS CHECK" not in output:
                raise AssertionError(f"Falhou {label} {mode}\n{output}")
            checks.append({"file": label, "mode": mode, "exitCode": run.returncode,
                           "output": output})
            print(f"OK {mode}: {label}", flush=True)

    check(ROOT / "contrato/VERIFICAR.bend", "contrato/VERIFICAR.bend")
    check(HERE / "NucleoVerificar.bend", "tests/proof/NucleoVerificar.bend")
    for example, program, proof in CASES:
        label = f"examples/{example}/{program}.bend + {proof}.bend + Seed.bend"
        with tempfile.TemporaryDirectory(prefix="jaydb2-revisao-") as temporary:
            folder = Path(temporary)
            generated_cases[label] = stage(folder, example, program, proof)
            check(folder / "Verificar.bend", label)
    if sources() != source_hashes:
        raise AssertionError("Fontes mudaram durante a verificacao; execute novamente")
    report = {
        "checkedAt": datetime.now(timezone.utc).isoformat(),
        "contractRevision": "tres-tamanhos-sem-orcamentos-fisicos-v2",
        "compiler": str(compiler), "version": version, "compilerSha256": digest(compiler),
        "kernelSha256": digest(Path(env["BENDTT"])) if env.get("BENDTT") else None,
        "durationSeconds": round(time.monotonic() - started, 3),
        "harnessTimeoutIsDevelopmentOnly": True,
        "fullExecutableContractProved": False,
        "scope": "Contrato, wrappers puros com o mesmo Codec e certificados/terminacao/seeds de seis exemplos; sem execucao nativa ou Ambiente instanciado; nao inclui o lote legado de 222 casos fechados",
        "checks": checks, "sourcesSha256": source_hashes,
        "generatedTestModules": generated_cases,
    }
    if args.record:
        (HERE / "REVISAO_RECURSOS_SIMPLES.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print(f"{len(checks)} verificacoes da revisao OK", flush=True)


if __name__ == "__main__":
    main()
