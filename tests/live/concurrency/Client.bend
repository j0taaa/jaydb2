import Base
import ./Data.bend as D
import ./Semantics.bend as S

type Command is Data:
  Read{key: String}
  Increment{key: String}
  Transfer{from: String, to: String}
  Invalid{}

def command(args: D.Value) -> Command:
  match args:
    case D.VText{key}: Read{key}
    case D.VList{D.VText{key}, D.VListEmpty{}}: Increment{key}
    case D.VList{D.VText{from}, D.VList{D.VText{to}, D.VListEmpty{}}}: Transfer{from, to}
    case _: Invalid{}

def refused() -> S.Action:
  S.Refuse{D.VAbsent{}}

def accepted(k: U32 -> S.Action, low: U32, valid: Bool) -> S.Action:
  match valid:
    case False{}: refused()
    case True{}: k(low)

# The fixture uses small unsigned balances carried in the low word.
def cell(k: U32 -> S.Action, v: D.Value) -> S.Action:
  match v:
    case D.VInt{high, low}: accepted(k, low, U32.is_eq(high, 0))
    case _: refused()

def observed(k: U32 -> S.Action, o: D.Observation) -> S.Action:
  match o:
    case D.Cell{v}: cell(k, v)
    case _: refused()

def value(k: U32 -> S.Action, r: S.Return) -> S.Action:
  match r:
    case S.Datum{o}: observed(k, o)
    case S.UnitValue{}: refused()

def read(key: String, k: U32 -> S.Action) -> S.Action:
  S.Access{D.ReadCell{D.Application{"counters"}, key, "value"}, r => value(k, r)}

def write(key: String, low: U32, next: S.Action) -> S.Action:
  S.Access{D.DefineColumn{D.Application{"counters"}, key, "value", D.VInt{0, low}},
    r => next}

def show(low: U32) -> S.Action:
  S.Finish{D.VInt{0, low}}

def increment_value(key: String, +old: U32, overflow: Bool) -> S.Action:
  match overflow:
    case False{}: write(key, (old + 1 : U32), show((old + 1 : U32)))
    case True{}: refused()

def increment(+key: String) -> S.Action:
  read(key, +old => increment_value(key, old, U32.is_eq(old, 4294967295)))

def moved(from: String, to: String, left: U32, right: U32, blocked: Bool) -> S.Action:
  match blocked:
    case False{}: write(from, (left - 1 : U32), write(to, (right + 1 : U32), S.Finish{D.VAbsent{}}))
    case True{}: refused()

def move_values(from: String, to: String, +left: U32, +right: U32) -> S.Action:
  moved(from, to, left, right, U32.is_eq(left, 0) || U32.is_eq(right, 4294967295))

def transferred(+from: String, +to: String, same: Bool) -> S.Action:
  match same:
    case False{}: read(from, left => read(to, right => move_values(from, to, left, right)))
    case True{}: refused()

def transfer(+from: String, +to: String) -> S.Action:
  transferred(from, to, String.eq(from, to))

def execute(c: Command) -> S.Action:
  match c:
    case Read{key}: read(key, show)
    case Increment{key}: increment(key)
    case Transfer{from, to}: transfer(from, to)
    case Invalid{}: refused()

def start(ctx: D.Context, args: D.Value) -> S.Action:
  execute(command(args))

def program() -> S.Program:
  S.Program{start}
