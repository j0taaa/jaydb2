# One read or key enumeration, separately certified for the pinned-root lane.
import Base
import ./Data.bend as D
import ./Semantics.bend as S

def arg(args: D.Value, n: Nat) -> D.Value:
  match args n:
    case D.VList{v, rest} Zero{}: v
    case D.VList{v, rest} Succ{p}: arg(rest, p)
    case _ _: D.VAbsent{}

def text(v: D.Value) -> String:
  match v:
    case D.VText{s}: s
    case _: ""

def selected(keys: Bool, table: String, key: String, column: String) -> D.Operation:
  match keys:
    case True{}: D.EnumerateKeys{D.Application{table}}
    case False{}: D.ReadCell{D.Application{table}, key, column}

def operation(+args: D.Value) -> D.Operation:
  selected(String.eq(text(arg(args, 0n)), "keys"), text(arg(args, 1n)),
    text(arg(args, 2n)), text(arg(args, 3n)))

def keys(xs: List<&2, String>) -> D.Value:
  match xs:
    case Nil{}: D.VListEmpty{}
    case Con{key, rest}: D.VList{D.VText{key}, keys(rest)}

def value(r: S.Return) -> D.Value:
  match r:
    case S.Datum{D.Cell{v}}: v
    case S.Datum{D.Keys{xs}}: keys(xs)
    case _: D.VAbsent{}

def program() -> S.Program:
  S.Program{ctx => args => S.Access{operation(args), r => S.Finish{value(r)}}}
