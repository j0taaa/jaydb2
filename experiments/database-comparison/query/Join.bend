# One inner-join transaction over every actual child key. Missing parents skip.
import Base
import ./Data.bend as D
import ./Semantics.bend as S

def reverse(xs: D.Value, out: D.Value) -> D.Value:
  match xs:
    case D.VList{x, rest}: reverse(rest, D.VList{x, out})
    case _: out

def pair(key: String, value: D.Value) -> D.Value:
  D.VList{D.VText{key}, D.VList{value, D.VListEmpty{}}}

def parent_return(+key: String, +out: D.Value, done: D.Value -> S.Action, r: S.Return) -> S.Action:
  match r:
    case S.Datum{D.Cell{v}}: done(D.VList{pair(key, v), out})
    case S.Datum{D.RowAbsent{}}: done(out)
    case _: S.Refuse{D.VText{"unexpected parent return"}}

def foreign_return(+key: String, parent: String, column: String, out: D.Value,
  done: D.Value -> S.Action, r: S.Return) -> S.Action:
  match r:
    case S.Datum{D.Cell{D.VText{target}}}:
      S.Access{D.ReadCell{D.Application{parent}, target, column}, parent_return(key, out, done)}
    case _: S.Refuse{D.VText{"join requires text foreign keys"}}

def walk(xs: List<&2, String>, +child: String, +foreign: String,
  +parent: String, +column: String, out: D.Value) -> S.Action:
  match xs:
    case Nil{}: S.Finish{reverse(out, D.VListEmpty{})}
    case Con{+key, +rest}:
      S.Access{D.ReadCell{D.Application{child}, key, foreign},
        foreign_return(key, parent, column, out,
          next => walk(rest, child, foreign, parent, column, next))}

def listed(+child: String, +foreign: String, +parent: String, +column: String, r: S.Return) -> S.Action:
  match r:
    case S.Datum{D.Keys{keys}}: walk(keys, child, foreign, parent, column, D.VListEmpty{})
    case _: S.Refuse{D.VText{"unexpected keys return"}}

type Command is Data:
  Join{child: String, foreign: String, parent: String, column: String}
  Invalid{}

def analyze(args: D.Value) -> Command:
  match args:
    case D.VList{D.VText{"join"}, D.VList{D.VText{child}, D.VList{D.VText{foreign}, D.VList{D.VText{parent}, D.VList{D.VText{column}, D.VListEmpty{}}}}}}: Join{child, foreign, parent, column}
    case _: Invalid{}

def command(p: Command) -> S.Action:
  match p:
    case Join{+child, +foreign, +parent, +column}:
      S.Access{D.EnumerateKeys{D.Application{child}}, listed(child, foreign, parent, column)}
    case Invalid{}: S.Refuse{D.VText{"expected [join, child, foreign_key, parent, parent_column]"}}

def start(ctx: D.Context, args: D.Value) -> S.Action:
  command(analyze(args))

def program() -> S.Program:
  S.Program{start}
