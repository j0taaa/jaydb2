# Read-only CONSTRUCTION helpers. This proof is independent of authorization.
# No recursive higher-order syntax, lowering, general bind or hidden callbacks.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Logic.bend as L
import ../src/ReadOnly.bend as RO
import ./Query.bend as Q
import ./Laws.bend as G

def cell_result(r: S.Return) -> S.Action:
  match r:
    case S.Datum{D.Cell{value}}: S.Finish{value}
    case S.Datum{D.RowAbsent{}}: S.Finish{D.VAbsent{}}
    case _: S.Refuse{D.VText{"unexpected cell return"}}

def cell(c: D.Collection, key: String, column: String) -> S.Action:
  S.Access{D.ReadCell{c, key, column}, cell_result}

def cell_result_readonly(r: S.Return) -> RO.Action(1n, cell_result(r)):
  match r:
    case S.Datum{D.Cell{v}}: Unit{}
    case S.Datum{D.RowAbsent{}}: Unit{}
    case S.Datum{D.Existence{b}}: Unit{}
    case S.Datum{D.Count{n}}: Unit{}
    case S.Datum{D.Keys{xs}}: Unit{}
    case S.UnitValue{}: Unit{}

law cell_readonly:
  for c: D.Collection
  for key: String
  for column: String
  RO.Action(2n, cell(c, key, column))
def cell_readonly(c, key, column):
  L.Both{Unit{}, r => cell_result_readonly(r)}

def selected(result: Q.Selection) -> S.Action:
  match result:
    case Q.Selected{record}: S.Finish{record}
    case Q.MissingRow{}: S.Finish{D.VAbsent{}}
    case Q.InvalidFields{}: S.Refuse{D.VText{"invalid fields"}}
    case Q.UnexpectedReturn{}: S.Refuse{D.VText{"unexpected selection return"}}

def selected_readonly(result: Q.Selection) -> RO.Action(1n, selected(result)):
  match result:
    case Q.Selected{v}: Unit{}
    case Q.MissingRow{}: Unit{}
    case Q.InvalidFields{}: Unit{}
    case Q.UnexpectedReturn{}: Unit{}

# Every Return continuation is required, not just observed successful returns.
def fields_readonly(xs: List<&2, String>, +n: Nat, +c: D.Collection, +key: String,
  -done: Q.Selection -> S.Action, h: @result: Q.Selection -> RO.Action(n, done(result))) ->
  RO.Action(G.depth(xs, n), Q.read_fields(c, key, xs, done)):
  match xs:
    case Nil{}: h(Q.Selected{D.VRecordEmpty{}})
    case Con{+name, +rest}:
      L.Both{Unit{}, +r => fields_readonly(rest, n, c, key,
        result => done(Q.combine(name, r, result)), result => h(Q.combine(name, r, result)))}

def invalid_readonly(xs: List<&2, String>) -> RO.Action(G.depth(xs, 1n), selected(Q.InvalidFields{})):
  match xs:
    case Nil{}: Unit{}
    case Con{name, rest}: Unit{}

def select(c: D.Collection, key: String, fields: List<&2, String>) -> S.Action:
  Q.select(c, key, fields, selected)

def select_choice_readonly(valid: Bool, +xs: List<&2, String>, c: D.Collection, key: String) ->
  RO.Action(G.depth(xs, 1n), Q.select_valid(valid, c, key, xs, selected)):
  match valid:
    case True{}: fields_readonly(xs, 1n, c, key, selected, result => selected_readonly(result))
    case False{}: invalid_readonly(xs)

law select_readonly:
  for c: D.Collection
  for key: String
  for +fields: List<&2, String>
  RO.Action(G.depth(fields, 1n), select(c, key, fields))
def select_readonly(c, key, fields):
  select_choice_readonly(Q.fields_valid(fields), fields, c, key)

# A small closed program: VText argument names a row in the user's own table.
# No program registration or execution route is altered by this module.
def start(fields: List<&2, String>, ctx: D.Context, args: D.Value) -> S.Action:
  match args:
    case D.VText{key}: select(D.Application{D.context_id(ctx)}, key, fields)
    case _: S.Refuse{D.VText{"expected text key"}}

def program(fields: List<&2, String>) -> S.Program:
  S.Program{start(fields)}

def start_readonly(+fields: List<&2, String>, ctx: D.Context, args: D.Value) ->
  &n: Nat -> RO.Action(n, start(fields, ctx, args)):
  match args:
    case D.VText{key}: (G.depth(fields, 1n), select_readonly(D.Application{D.context_id(ctx)}, key, fields))
    case D.VAbsent{}: (1n, Unit{})
    case D.VBool{b}: (1n, Unit{})
    case D.VInt{h,l}: (1n, Unit{})
    case D.VListEmpty{}: (1n, Unit{})
    case D.VList{h,t}: (1n, Unit{})
    case D.VRecordEmpty{}: (1n, Unit{})
    case D.VRecord{n,v,r}: (1n, Unit{})

law program_readonly:
  for +fields: List<&2, String>
  RO.Program(program(fields))
def program_readonly(fields):
  ctx => args => start_readonly(fields, ctx, args)
