# Administrator law TEMPLATES, never installed implicitly or assumed proved.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Logic.bend as L

# A relation row's named field must reference an existing target row.
def ReferenceValue(targets: List<&2, D.Row>, value: Maybe<&2, D.Value>) -> Type:
  match value:
    case Some{D.VText{key}}: {D.exists_row(D.find_row(targets, key)) == True{} : Bool}
    case _: Empty


def Reference(targets: List<&2, D.Row>, field: String, row: D.Row) -> Type:
  D.Row{k, fs} = row
  ReferenceValue(targets, D.find_field(fs, field))

def References(+targets: List<&2, D.Row>, +field: String, rows: List<&2, D.Row>) -> Type:
  match rows:
    case Nil{}: Unit
    case Con{row, rest}: L.E<Reference(targets, field, row), References(targets, field, rest)>

# Exact index maintenance: caller's pure canonical build determines ALL rows.
# Equality is propositional, not a hash or user-supplied Boolean certificate.
def ExactRows(~build: List<&2, D.Row> -> List<&2, D.Row>,
  base: Maybe<&2, List<&2, D.Row>>, index: Maybe<&2, List<&2, D.Row>>) -> Type:
  match base index:
    case Some{rows} Some{actual}: {actual == build(rows) : List<&2, D.Row>}
    case _ _: Empty


def ExactIndex(~build: List<&2, D.Row> -> List<&2, D.Row>, base: D.Collection,
  index: D.Collection, +state: D.State) -> Type:
  ExactRows(~build, D.rows_collection(base, state), D.rows_collection(index, state))

# Explicitly permits transient inconsistency; requires it at every stable
# state and on successful close. Other installed laws still govern accesses.
def OnStable(~invariant: D.State -> Type, h: S.Situation) -> Type:
  match h:
    case S.Stable{s}: invariant(s)
    case S.Executing{s, ctx, code, args, w, ts}: Unit
    case S.Closed{s, ctx, code, args, w, ts, S.Response{S.Success{}, v}}: invariant(w)
    case S.Closed{s, ctx, code, args, w, ts, r}: Unit

def OnEveryPrefix(~invariant: D.State -> Type, h: S.Situation) -> Type:
  match h:
    case S.Stable{s}: invariant(s)
    case S.Executing{s, ctx, code, args, w, ts}: invariant(w)
    case S.Closed{s, ctx, code, args, w, ts, r}: invariant(w)
