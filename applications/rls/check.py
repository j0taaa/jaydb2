#!/usr/bin/env python3
"""Both official proof modes, causal negative fixtures, and the native host.

Caller holds /tmp/jaydb2-experiments-heavy.lock and sets unlimited stack.
All generated artifacts stay under this application's ignored .build directory.
"""
import argparse
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
APP = Path(__file__).resolve().parent
BUILD = APP / '.build'
sys.path.insert(0, str(ROOT))
from tools.bend import environment, executable


def prepare(directory):
    directory.mkdir(parents=True, exist_ok=True)
    for source in APP.glob('*.bend'):
        (directory / source.name).write_text(source.read_text())
    for name in ('Orders', 'Foundations'):
        (directory / f'{name}.bend').write_text(
            (ROOT / 'proof' / f'{name}.bend').read_text().replace('../contract/', './'))
    for name in ('Laws', 'Query', 'Action'):
        (directory / f'{name}.bend').write_text(
            (ROOT / 'library' / f'{name}.bend').read_text()
            .replace('../contract/', './').replace('../src/', './'))


def literal(s):
    return '"' + ''.join('\\"' if c == '"' else '\\\\' if c == '\\'
        else f'\\u{{{ord(c):02x}}}' if ord(c) < 32 else c for c in s) + '"'


def proof_root(name='positive', code=None, proof=None, universal=False):
    d = BUILD / name
    prepare(d)
    if code is not None:
        (d / 'Client.bend').write_text(code)
    if proof is not None:
        (d / 'ClientProof.bend').write_text(proof)
    for source in (ROOT / 'contract').glob('*.bend'):
        (d / source.name).write_text(source.read_text())
    for name in ('ReadOnly', 'Termination', 'ValidationFinal'):
        (d / f'{name}.bend').write_text(
            (ROOT / 'src' / f'{name}.bend').read_text().replace('../contract/', './'))
    (d / 'Environment.bend').write_text('import Base\ndef identity() -> String: "rls-proof"\n')
    (d / 'Instance.bend').write_text('''import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Configuration.bend as C
def config() -> S.Configuration: C.config()
def context() -> D.Context: D.Context{"alice", "user"}
def arguments() -> D.Value: D.VList{D.VText{"list"}, D.VListEmpty{}}
''')
    target = ('@ctx: D.Context -> @args: D.Value -> R.Certifies(I.config(), code(), Client.program(), ctx, args)'
              if universal else 'R.Certifies(I.config(), code(), Client.program(), I.context(), I.arguments())')
    (d / 'Bindings.bend').write_text('''import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Requirements.bend as R
import ./RequestFacts.bend as F
import ./Client.bend as Client
import ./Instance.bend as I
''' + 'def code() -> String: ' + literal((d / 'Client.bend').read_text()) + '\n'
        + 'law certificate: ' + target + '\n'
        + 'law terminates: F.ProgramTerminates(I.config(), Client.program())\n')
    (d / 'Check.bend').write_text('import ./ClientProof.bend as Proof\nimport ./Seed.bend as Seed\n')
    return d / 'Check.bend'


def positive(root):
    subprocess.run([sys.executable, '-B', str(ROOT / 'tools/check.py'), '--timeout', '120', str(root)],
                   check=True, cwd=ROOT)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--proof-only', action='store_true')
    args = parser.parse_args()
    BUILD.mkdir(exist_ok=True)
    positive(proof_root())
    from negative_cases import cases, rejected
    for name, code, proof, expected in cases():
        rejected(name, proof_root(name, code, proof), expected)
    from test import universal_proof
    positive(proof_root('universal', proof=universal_proof(), universal=True))
    if not args.proof_only:
        from test import native_session
        native_session()


if __name__ == '__main__':
    main()
