#!/usr/bin/env python3
"""Check the directory-model spike, NOT an admitted unbounded application.

Caller holds the repository heavy-command lock and sets unlimited stack.
Artifacts stay in applications/rls/.build/unbounded-*.
"""
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import check as rls
from negative_cases import rejected


def proof_root(name='unbounded-algebra', negative=None):
    root = rls.proof_root(name)
    for path in HERE.glob('*.bend'):
        (root.parent / path.name).write_text(path.read_text())
    if negative is None:
        root.write_text('import ./DirectoryProof.bend as DirectoryProof\nimport ./Examples.bend as Examples\n')
    else:
        (root.parent / 'Counterexample.bend').write_text(negative)
        root.write_text('import ./Counterexample.bend as Counterexample\n')
    return root


def counterexamples():
    notes = 'D.Application{"notes"}'
    empty = 'M.state(Nil{},Nil{})'
    one = 'M.state([Some{"one"}],Nil{})'
    variants = (
        ('omitted-directory', empty,
         f'D.DefineRow{{{notes},"alice/z",M.fields(M.Alice{{}},"alice/z","one")}}', '"+"', '""'),
        ('removed-entry-only', one,
         f'D.DefineRow{{{notes},"alice/_dir",M.fields(M.Alice{{}},"alice/_dir","")}}', '"+"', '""'),
        ('foreign-id-in-directory', one,
         f'D.DefineRow{{{notes},"alice/_dir",M.fields(M.Alice{{}},"alice/_dir","bob/z")}}', '"+"', '"bob/z"'),
        ('extra-directory-position', one,
         f'D.DefineRow{{{notes},"alice/_dir",M.fields(M.Alice{{}},"alice/_dir","++")}}', '"+"', '"++"'),
    )
    for name, before, operation, expected, observed in variants:
        source = '''import Base
import ./Data.bend as D
import ./Model.bend as M
import ./Configuration.bend as C
# Sole intended failure: actual operation leaves the directory text unequal to
# the exact text for the unchanged/resulting business rows. This is a MODEL
# equality control, not a filled certificate for the client application.
def directory_row(m:Maybe<&2,D.Row>) -> Maybe<&2,D.Value>:
  match m:
    case None{}: None{}
    case Some{D.Row{k,fs}}: D.find_field(fs,"text")

def directory_rows(m:Maybe<&2,List<&2,D.Row>>) -> Maybe<&2,D.Value>:
  match m:
    case None{}: None{}
    case Some{rows}: directory_row(D.find_row(rows,"alice/_dir"))

def directory_text(res:D.ResultOp) -> Maybe<&2,D.Value>:
  match res:
    case D.Changed{s}: directory_rows(D.rows_collection(D.Application{"notes"},s))
    case _: None{}

law false:
  {directory_text(D.operate(C.schema(),''' + before + ',' + operation + ''')) ==
    Some{D.VText{"+"}} : Maybe<&2,D.Value>}
def false(): {==}
'''
        yield name, source, (f'D.VText{{{expected}}}', f'D.VText{{{observed}}}')


def main():
    rls.positive(proof_root())
    for name, source, expected in counterexamples():
        label = 'unbounded-' + name
        rejected(label, proof_root(label, source), expected)


if __name__ == '__main__':
    main()
