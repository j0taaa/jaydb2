"""Filled false certificates: each fails ONLY at its named `false` obligation.

Every fixture is a complete certificate for its actual one-operation program,
built from the real Proofs/Directory machinery. Only `false` is wrong: either
the operation's permission, or the directory law after the actual write.
No stale positive command proof, missing import, hole, or forged axiom is used.
"""
from pathlib import Path
import re
import subprocess

APP = Path(__file__).resolve().parent
NOTES = 'D.Application{"notes"}'


def fields(key, owner, text=None):
    out = f'[D.Field{{"id", D.VText{{"{key}"}}}}, D.Field{{"owner", D.VText{{"{owner}"}}}}'
    return out + (f', D.Field{{"text", D.VText{{"{text}"}}}}]' if text is not None else ']')


def program(operation, terminal, extra=''):
    return '''import Base
import ./Data.bend as D
import ./Semantics.bend as S
''' + extra + '''def operation() -> D.Operation:
  ''' + operation + '''
def terminal() -> S.Action:
  ''' + terminal + '''
def program() -> S.Program:
  S.Program{ctx => args => S.Access{operation(), r => terminal()}}
'''


# A refused program needs no directory law; only its access permission.
PERMISSION = '''def refused(res: D.ResultOp, +m: Nat, +e: D.Schema, +s: D.State) ->
  H.Step(res, s, r => w => H.Safe(m, e, I.context(), w, Client.terminal())):
  match res:
    case D.FailureData{}: Unit{}
    case D.Observed{o}: Unit{}
    case D.Changed{w}: Unit{}

def step_safe(+d: Nat, +e: D.Schema, +s: D.State, dir: P.Directory(s), +owners: P.Owners(s)) ->
  H.Safe(d, e, I.context(), s, S.start(Client.program(), I.context(), I.arguments())):
  H.access(d, e, I.context(), s, Client.operation(), r => Client.terminal(), false(), +m =>
    refused(D.operate(e, s, Client.operation()), m, e, s))
'''

# Write a note but no directory entry: the directory law fails for alice.
ORPHAN = '''def step_safe(+d: Nat, +e: D.Schema, +s: D.State, dir: P.Directory(s), +owners: P.Owners(s)) ->
  H.Safe(d, e, I.context(), s, S.start(Client.program(), I.context(), I.arguments())):
  H.access(d, e, I.context(), s, Client.operation(), r => Client.terminal(), P.Both{{==}, P.Both{P.Both{{==}, {==}}, {==}}}, +m =>
    H.written(m, e, I.context(), s, D.Application{"notes"}, Shape.RowUpsert{"alice/00000099", Client.fields()}, r => Client.terminal(), +ns => +found =>
      orphan(s, ns, found, dir, owners)))

def orphan(+s: D.State, +ns: List<&2, D.Row>,
  +found: {D.rows_collection(D.Application{"notes"}, s) == Some{ns} : Maybe<&2, List<&2, D.Row>>},
  dir: P.Directory(s), +owners: P.Owners(s)) ->
  P.Directory(Dir.first(s, Shape.RowUpsert{"alice/00000099", Client.fields()}, ns)):
  L.Both{ha, hb} = dir
  +en = Dir.found_rows("notes", s, ns, found)
  +n2 = Dir.swapped("notes", s, ns, D.insert_row(ns, D.Row{"alice/00000099", Client.fields()}), found)
  +a2 = Dir.framed("notes", "alice_dir", s, D.insert_row(ns, D.Row{"alice/00000099", Client.fields()}), {==})
  +b2 = Dir.framed("notes", "bob_dir", s, D.insert_row(ns, D.Row{"alice/00000099", Client.fields()}), {==})
  L.Both{
    Dir.cast("alice", P.rows("alice_dir", s), P.rows("alice_dir", Dir.first(s, Shape.RowUpsert{"alice/00000099", Client.fields()}, ns)),
      D.insert_row(ns, D.Row{"alice/00000099", Client.fields()}), P.rows("notes", Dir.first(s, Shape.RowUpsert{"alice/00000099", Client.fields()}, ns)),
      Equal.sym(List<&2, D.Row>, P.rows("alice_dir", Dir.first(s, Shape.RowUpsert{"alice/00000099", Client.fields()}, ns)), P.rows("alice_dir", s), a2),
      Equal.sym(List<&2, D.Row>, P.rows("notes", Dir.first(s, Shape.RowUpsert{"alice/00000099", Client.fields()}, ns)), D.insert_row(ns, D.Row{"alice/00000099", Client.fields()}), n2),
      false(P.rows("alice_dir", s), ns, Dir.cast("alice", P.rows("alice_dir", s), P.rows("alice_dir", s), P.rows("notes", s), ns, {==}, en, ha))),
    Dir.cast("bob", P.rows("bob_dir", s), P.rows("bob_dir", Dir.first(s, Shape.RowUpsert{"alice/00000099", Client.fields()}, ns)),
      D.insert_row(ns, D.Row{"alice/00000099", Client.fields()}), P.rows("notes", Dir.first(s, Shape.RowUpsert{"alice/00000099", Client.fields()}, ns)),
      Equal.sym(List<&2, D.Row>, P.rows("bob_dir", Dir.first(s, Shape.RowUpsert{"alice/00000099", Client.fields()}, ns)), P.rows("bob_dir", s), b2),
      Equal.sym(List<&2, D.Row>, P.rows("notes", Dir.first(s, Shape.RowUpsert{"alice/00000099", Client.fields()}, ns)), D.insert_row(ns, D.Row{"alice/00000099", Client.fields()}), n2),
      Dir.save_other("bob", P.rows("bob_dir", s), ns, "alice/00000099", Client.fields(), O.users(s), "notes",
        Dir.notes_rows(s, ns, found, owners), {==}, {==}, Dir.cast("bob", P.rows("bob_dir", s), P.rows("bob_dir", s), P.rows("notes", s), ns, {==}, en, hb)))}
'''

# Remove alice's directory entry but keep the note: the law fails for alice.
UNLISTED = '''def step_safe(+d: Nat, +e: D.Schema, +s: D.State, dir: P.Directory(s), +owners: P.Owners(s)) ->
  H.Safe(d, e, I.context(), s, S.start(Client.program(), I.context(), I.arguments())):
  H.access(d, e, I.context(), s, Client.operation(), r => Client.terminal(), P.Both{{==}, P.Both{{==}, {==}}}, +m =>
    H.written(m, e, I.context(), s, D.Application{"alice_dir"}, Shape.RowDelete{"alice/00000001"}, r => Client.terminal(), +ds => +found =>
      unlisted(s, ds, found, dir)))

def unlisted(+s: D.State, +ds: List<&2, D.Row>,
  +found: {D.rows_collection(D.Application{"alice_dir"}, s) == Some{ds} : Maybe<&2, List<&2, D.Row>>}, dir: P.Directory(s)) ->
  P.Directory(D.swap_collection(D.Application{"alice_dir"}, s, D.remove_row(ds, "alice/00000001"))):
  L.Both{ha, hb} = dir
  +ed = Dir.found_rows("alice_dir", s, ds, found)
  +d2 = Dir.swapped("alice_dir", s, ds, D.remove_row(ds, "alice/00000001"), found)
  +n2 = Dir.framed("alice_dir", "notes", s, D.remove_row(ds, "alice/00000001"), {==})
  +b2 = Dir.framed("alice_dir", "bob_dir", s, D.remove_row(ds, "alice/00000001"), {==})
  L.Both{
    Dir.cast("alice", D.remove_row(ds, "alice/00000001"), P.rows("alice_dir", D.swap_collection(D.Application{"alice_dir"}, s, D.remove_row(ds, "alice/00000001"))),
      P.rows("notes", s), P.rows("notes", D.swap_collection(D.Application{"alice_dir"}, s, D.remove_row(ds, "alice/00000001"))),
      Equal.sym(List<&2, D.Row>, P.rows("alice_dir", D.swap_collection(D.Application{"alice_dir"}, s, D.remove_row(ds, "alice/00000001"))), D.remove_row(ds, "alice/00000001"), d2),
      Equal.sym(List<&2, D.Row>, P.rows("notes", D.swap_collection(D.Application{"alice_dir"}, s, D.remove_row(ds, "alice/00000001"))), P.rows("notes", s), n2),
      false(ds, P.rows("notes", s), Dir.cast("alice", P.rows("alice_dir", s), ds, P.rows("notes", s), P.rows("notes", s), ed, {==}, ha))),
    Dir.cast("bob", P.rows("bob_dir", s), P.rows("bob_dir", D.swap_collection(D.Application{"alice_dir"}, s, D.remove_row(ds, "alice/00000001"))),
      P.rows("notes", s), P.rows("notes", D.swap_collection(D.Application{"alice_dir"}, s, D.remove_row(ds, "alice/00000001"))),
      Equal.sym(List<&2, D.Row>, P.rows("bob_dir", D.swap_collection(D.Application{"alice_dir"}, s, D.remove_row(ds, "alice/00000001"))), P.rows("bob_dir", s), b2),
      Equal.sym(List<&2, D.Row>, P.rows("notes", D.swap_collection(D.Application{"alice_dir"}, s, D.remove_row(ds, "alice/00000001"))), P.rows("notes", s), n2), hb)}
'''

LAW_ORPHAN = '''law false:
  for +ds: List<&2, D.Row>
  for +ns: List<&2, D.Row>
  for h: P.Agree("alice", ds, ns)
  P.Agree("alice", ds, D.insert_row(ns, D.Row{"alice/00000099", Client.fields()}))
def false(ds, ns, h):
  +k => h(k)
'''

LAW_UNLISTED = '''law false:
  for +ds: List<&2, D.Row>
  for +ns: List<&2, D.Row>
  for h: P.Agree("alice", ds, ns)
  P.Agree("alice", D.remove_row(ds, "alice/00000001"), ns)
def false(ds, ns, h):
  +k => h(k)
'''


def law_allowed(witness):
    return 'law false:\n  P.Allowed(I.context(), Client.operation())\ndef false():\n  ' + witness + '\n'


def cases():
    original = (APP / 'ClientProof.bend').read_text()
    imports = original[:original.index('# Per-principal facts')]
    certify = original[original.index('# The quantified state'):original.index('# Termination on arbitrary')]
    tail = '''def B.certificate(s, valid, identity, n):
  L.Both{structure, L.Both{+owners, L.Both{dir, rest}}} = valid
  +s = s
  +n = n
  certify(I.context(), I.arguments(), B.code(), s, owners, identity, n, step_safe(Succ{n}, C.schema(), s, dir, owners))

def B.terminates(s, ctx, args):
  T.program_finite(2n, Client.program(), C.schema(), s, ctx, args, r => Unit{})
'''
    refuse = 'S.Refuse{D.VText{"attempted"}}'
    write = P = 'P.Both{{==}, P.Both{P.Both{{==}, {==}}, {==}}}'
    variants = (
        ('read-bob', program(f'D.ReadCell{{{NOTES}, "bob/00000001", "text"}}', refuse),
         law_allowed('P.Both{{==}, P.Both{{==}, {==}}}') + PERMISSION, ('"bob"', '"alice"')),
        ('update-bob', program(f'D.DefineRow{{{NOTES}, "bob/00000001", {fields("bob/00000001", "bob", "forged")}}}', refuse),
         law_allowed(write) + PERMISSION, ('"bob"', '"alice"')),
        ('insert-bob-owner', program(f'D.DefineRow{{{NOTES}, "alice/00000099", {fields("alice/00000099", "bob", "forged")}}}', refuse),
         law_allowed(write) + PERMISSION, ('D.VText{"bob"}', 'D.VText{"alice"}')),
        ('transfer-owner', program(f'D.DefineRow{{{NOTES}, "alice/00000001", {fields("alice/00000001", "bob", "forged")}}}', refuse),
         law_allowed(write) + PERMISSION, ('D.VText{"bob"}', 'D.VText{"alice"}')),
        ('scan-all', program(f'D.EnumerateKeys{{{NOTES}}}', refuse),
         law_allowed('{==}') + PERMISSION, ('"notes"', '"alice_dir"')),
        ('read-bob-directory', program('D.EnumerateKeys{D.Application{"bob_dir"}}', refuse),
         law_allowed('{==}') + PERMISSION, ('"bob_dir"', '"alice_dir"')),
        ('foreign-id-in-directory', program(f'D.DefineRow{{D.Application{{"alice_dir"}}, "bob/00000001", {fields("bob/00000001", "bob")}}}', refuse),
         law_allowed(write) + PERMISSION, ('"bob"', '"alice"')),
        ('create-without-directory', program(f'D.DefineRow{{{NOTES}, "alice/00000099", fields()}}', 'S.Finish{D.VText{"alice/00000099"}}',
         'def fields() -> List<&2, D.Field>:\n  ' + fields('alice/00000099', 'alice', 'orphan') + '\n'),
         LAW_ORPHAN + ORPHAN, ('D.insert_row', '"alice/00000099"')),
        ('unlist-without-delete', program('D.RemoveRow{D.Application{"alice_dir"}, "alice/00000001"}', 'S.Finish{D.VText{"alice/00000001"}}'),
         LAW_UNLISTED + UNLISTED, ('D.remove_row', '"alice/00000001"')),
    )
    for name, code, body, expected in variants:
        yield name, code, imports + body + '\n' + certify + tail, expected


def rejected(name, root, expected):
    from check import BUILD, environment, executable
    for mode in ('--check-only', '--verdict'):
        result = subprocess.run([str(executable()), str(root), mode], env=environment(),
                                capture_output=True, text=True, timeout=300)
        output = result.stdout + result.stderr
        (BUILD / f'{name}-{mode[2:]}.log').write_text(output)
        locations = re.findall(r'Location: ([^\s]+)', output)
        assert result.returncode and 'SOME PROOFS FAIL' in output, output
        assert locations and set(locations) == {'false'}, output
        assert '- expected :' in output and '- observed :' in output, output
        assert all(s in output for s in expected), output
        assert not any(s in output for s in ('a defined name', 'a filled definition',
            'a fresh name', 'a parsed term', 'stack overflow', 'stack overflowed', 'consumed more than once')), output
        print(f'OK intended {name} rejection {mode} at false', flush=True)
