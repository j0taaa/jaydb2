#!/usr/bin/env python3
"""Build a local proof-only application root; real session testing is separate."""
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'applications/tasks'))
import query_check


def main():
    directory = ROOT / 'build/library/application-proof'
    directory.mkdir(parents=True, exist_ok=True)
    query_check.prepare(directory, ROOT)
    for source in (ROOT / 'contract').glob('*.bend'):
        (directory / source.name).write_text(source.read_text())
    for name in ('Termination', 'ValidationFinal'):
        source = (ROOT / 'src' / f'{name}.bend').read_text()
        (directory / f'{name}.bend').write_text(source.replace('../contract/', './'))
    (directory / 'Environment.bend').write_text('import Base\ndef identity() -> String:\n  "library-proof-development"\n')
    (directory / 'Instance.bend').write_text('''import Base
import ./Data.bend as D
import ./Configuration.bend as C
import ./Semantics.bend as S
def config() -> S.Configuration: C.config()
def context() -> D.Context: D.Context{"alice", "user"}
def arguments() -> D.Value: D.VAbsent{}
''')
    code = (directory / 'Client.bend').read_text()
    literal = '"' + ''.join('\\"' if c == '"' else '\\\\' if c == '\\' else
                            f'\\u{{{ord(c):02x}}}' if ord(c) < 32 else c for c in code) + '"'
    (directory / 'Bindings.bend').write_text('''import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Requirements.bend as R
import ./Interface.bend as F
import ./Instance.bend as I
import ./Client.bend as Client

def code() -> String:
  ''' + literal + '''
law certificate:
  R.Certifies(I.config(), code(), Client.program(), I.context(), I.arguments())
law terminates:
  F.ProgramTerminates(I.config(), Client.program())
''')
    (directory / 'Check.bend').write_text('import ./ClientProof.bend as Proof\nimport ./Seed.bend as Seed\n')
    print(directory / 'Check.bend')


if __name__ == '__main__':
    main()
