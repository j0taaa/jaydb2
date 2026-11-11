"""Filled false certificates: each fails ONLY at its named access obligation.

The common prefix/publication proof is adapted to the actual one-access program.
No stale positive command proof, missing import, hole, or forged axiom is used.
"""
from pathlib import Path
import re
import subprocess

APP = Path(__file__).resolve().parent


def row(key, owner):
    return '[D.Field{"id", D.VText{"' + key + '"}}, D.Field{"owner", D.VText{"' + owner + '"}}, D.Field{"text", D.VText{"forged"}}]'


def cases():
    original = (APP / 'ClientProof.bend').read_text()
    imports = original[:original.index('# Authorization')]
    common = original[original.index('def owners_initial'):original.index('def B.certificate')]
    notes = 'D.Application{"notes"}'
    # The existing-row update and fresh-row insert use distinct keys in test.py.
    variants = (
        ('read-bob', f'D.ReadCell{{{notes}, "bob/1", "text"}}',
         'P.Both{{==}, P.Both{{==}, {==}}}', 'S.Refuse{D.VAbsent{}}', ('"bob"', '"alice"')),
        ('update-bob', f'D.DefineRow{{{notes}, "bob/1", {row("bob/1", "bob")}}}',
         'P.Both{{==}, P.Both{P.Both{{==}, {==}}, {==}}}', 'S.Finish{D.VAbsent{}}', ('"bob"', '"alice"')),
        ('insert-bob-owner', f'D.DefineRow{{{notes}, "alice/2", {row("alice/2", "bob")}}}',
         'P.Both{{==}, P.Both{P.Both{{==}, {==}}, {==}}}', 'S.Finish{D.VAbsent{}}', ('D.VText{"bob"}', 'D.VText{"alice"}')),
        ('transfer-owner', f'D.DefineRow{{{notes}, "alice/1", {row("alice/1", "bob")}}}',
         'P.Both{{==}, P.Both{P.Both{{==}, {==}}, {==}}}', 'S.Finish{D.VAbsent{}}', ('D.VText{"bob"}', 'D.VText{"alice"}')),
        ('scan-all', f'D.EnumerateKeys{{{notes}}}',
         'P.Both{{==}, {==}}', 'S.Finish{D.VListEmpty{}}', ('"user"', '"admin"')),
    )
    for name, op, witness, terminal, expected in variants:
        code = '''import Base
import ./Data.bend as D
import ./Semantics.bend as S
def operation() -> D.Operation:
  ''' + op + '''
def program() -> S.Program:
  S.Program{ctx => args => S.Access{operation(), r => ''' + terminal + '}}\n'
        proof = imports + '''# Intended and sole failure: the actual operation's permission.
law false:
  P.Allowed(I.context(), Client.operation())
def false():
  ''' + witness + '\n\n' + common + '''def B.certificate(s, valid, identity, n):
  certify(I.context(), I.arguments(), B.code(), s, valid, identity, n,
    L.Both{false(), r => Unit{}})

def B.terminates(s, ctx, args):
  T.program_finite(3n, Client.program(), C.schema(), s, ctx, args, r => Unit{})
'''
        yield name, code, proof, expected


def rejected(name, root, expected):
    from check import BUILD, environment, executable
    for mode in ('--check-only', '--verdict'):
        result = subprocess.run([str(executable()), str(root), mode], env=environment(),
                                capture_output=True, text=True, timeout=120)
        output = result.stdout + result.stderr
        (BUILD / f'{name}-{mode[2:]}.log').write_text(output)
        locations = re.findall(r'Location: ([^\s]+)', output)
        assert result.returncode and 'SOME PROOFS FAIL' in output, output
        assert locations and set(locations) == {'false'}, output
        assert '- expected :' in output and '- observed :' in output, output
        assert all(s in output for s in expected), output
        assert not any(s in output for s in ('a defined name', 'a filled definition',
            'a fresh name', 'a parsed term', 'stack overflow', 'consumed more than once')), output
        print(f'OK intended {name} rejection {mode} at false', flush=True)
