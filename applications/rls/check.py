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

# Unchanged generic row/collection/read lemmas from the ordinary library.
LIBRARY = ('RowLookupProofs', 'RowRemovalLookupProofs', 'CollectionFrameProofs',
           'MutationStateShapeProofs', 'ValueScalarProofs', 'Value', 'ReadOperationProofs')


def relocate(text):
    return text.replace('../contract/', './').replace('../src/', './').replace('../proof/', './')


def prepare(directory):
    directory.mkdir(parents=True, exist_ok=True)
    for source in APP.glob('*.bend'):
        (directory / source.name).write_text(source.read_text())
    for name in ('Orders', 'Foundations'):
        (directory / f'{name}.bend').write_text(relocate((ROOT / 'proof' / f'{name}.bend').read_text()))
    for name in LIBRARY:
        (directory / f'{name}.bend').write_text(relocate((ROOT / 'library' / f'{name}.bend').read_text()))


def literal(s):
    return '"' + ''.join('\\"' if c == '"' else '\\\\' if c == '\\'
        else f'\\u{{{ord(c):02x}}}' if ord(c) < 32 else c for c in s) + '"'


def chunked(s, size=2000):
    """The same string as a `++` chain: the pinned official translator for
    --verdict overflows its stack expanding one literal past ~5000 characters."""
    parts = [s[i:i + size] for i in range(0, len(s), size)] or ['']
    assert ''.join(parts) == s
    return ' ++ '.join(literal(part) for part in parts)


def proof_root(name='positive', code=None, proof=None, universal=False, context=('alice', 'user')):
    d = BUILD / name
    prepare(d)
    if code is not None:
        (d / 'Client.bend').write_text(code)
    if proof is not None:
        (d / 'ClientProof.bend').write_text(proof)
    for source in (ROOT / 'contract').glob('*.bend'):
        (d / source.name).write_text(source.read_text())
    for name in ('ReadOnly', 'Termination', 'ValidationFinal'):
        (d / f'{name}.bend').write_text(relocate((ROOT / 'src' / f'{name}.bend').read_text()))
    (d / 'Environment.bend').write_text('import Base\ndef identity() -> String: "rls-proof"\n')
    (d / 'Instance.bend').write_text('''import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Configuration.bend as C
def config() -> S.Configuration: C.config()
''' + 'def context() -> D.Context: D.Context{' + ', '.join(literal(part) for part in context) + '}\n' + '''
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
''' + 'def code() -> String: ' + chunked((d / 'Client.bend').read_text()) + '\n'
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
    for name, code, proof, expected, context in cases():
        rejected(name, proof_root(name, code, proof, context=context), expected)
    from test import universal_proof
    positive(proof_root('universal', proof=universal_proof(), universal=True))
    if not args.proof_only:
        from test import native_session
        native_session()


if __name__ == '__main__':
    main()
