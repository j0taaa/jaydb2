#!/usr/bin/env python3
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[2]
APP = Path(__file__).resolve().parent
LIBS = ('Action', 'Aggregate', 'Value', 'Int64', 'Key', 'Query', 'Read', 'Mutation', 'Index', 'Summary', 'TableLaws', 'Laws', 'ReadProgram')

def prepare(directory):
    directory.mkdir(parents=True, exist_ok=True)
    for source in APP.glob('*.bend'):
        (directory/source.name).write_text(source.read_text())
    for name in ('Orders','Foundations'):
        (directory/f'{name}.bend').write_text((ROOT/'proof'/f'{name}.bend').read_text().replace('../contract/','./'))
    for name in LIBS:
        source=(ROOT/'library'/f'{name}.bend').read_text()
        (directory/f'{name}.bend').write_text(source.replace('../contract/','./').replace('../src/','./'))


def proof_root(directory=None, code=None, proof=None, permissions=None):
    d=directory or ROOT/'build/library/indexed-proof'
    prepare(d)
    if code is not None: (d/'Client.bend').write_text(code)
    if proof is not None: (d/'ClientProof.bend').write_text(proof)
    if permissions is not None: (d/'PermissionProof.bend').write_text(permissions)
    for source in (ROOT/'contract').glob('*.bend'):
        (d/source.name).write_text(source.read_text())
    for name in ('ReadOnly','Termination','ValidationFinal'):
        (d/f'{name}.bend').write_text((ROOT/'src'/f'{name}.bend').read_text().replace('../contract/','./'))
    (d/'Environment.bend').write_text('import Base\ndef identity() -> String: "indexed-proof"\n')
    (d/'Instance.bend').write_text('import Base\nimport ./Data.bend as D\nimport ./Semantics.bend as S\nimport ./Configuration.bend as C\ndef config() -> S.Configuration: C.config()\ndef context() -> D.Context: D.Context{"alice","user"}\ndef arguments() -> D.Value: D.VList{D.VText{"set"},D.VList{D.VBool{True{}},D.VListEmpty{}}}\n')
    code=(d/'Client.bend').read_text()
    literal='"'+''.join('\\"' if c=='"' else '\\\\' if c=='\\' else f'\\u{{{ord(c):02x}}}' if ord(c)<32 else c for c in code)+'"'
    (d/'Bindings.bend').write_text('import Base\nimport ./Data.bend as D\nimport ./Semantics.bend as S\nimport ./Requirements.bend as R\nimport ./RequestFacts.bend as F\nimport ./Client.bend as Client\nimport ./Instance.bend as I\ndef code() -> String: '+literal+'\nlaw certificate: R.Certifies(I.config(),code(),Client.program(),I.context(),I.arguments())\nlaw terminates: F.ProgramTerminates(I.config(),Client.program())\n')
    (d/'Check.bend').write_text('import ./Model.bend as M\nimport ./CheckedActions.bend as H\nimport ./Completion.bend as Completion\nimport ./Configuration.bend as C\nimport ./'+('PermissionProof' if permissions is not None else 'ClientProof')+'.bend as Proof\nimport ./Seed.bend as Seed\n')
    return d/'Check.bend'

if __name__=='__main__':
    print(proof_root())
