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

def change(+args: D.Value) -> D.Operation:
  D.DefineColumn{D.Application{text(arg(args, 0n))}, text(arg(args, 1n)),
    text(arg(args, 2n)), arg(args, 3n)}

def program() -> S.Program:
  S.Program{ctx => +args => S.Access{change(arg(args, 0n)), r =>
    S.Access{change(arg(args, 1n)), r => S.Finish{D.VBool{True{}}}}}}
