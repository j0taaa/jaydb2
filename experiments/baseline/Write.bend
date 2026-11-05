import Base
import ./Data.bend as D
import ./Semantics.bend as S

def key(args: D.Value) -> String:
  match args:
    case D.VList{D.VText{k}, rest}: k
    case _: "missing"

def value(args: D.Value) -> D.Value:
  match args:
    case D.VList{k, D.VList{v, rest}}: v
    case _: D.VAbsent{}

def program() -> S.Program:
  S.Program{ctx => +args =>
    S.Access{D.DefineColumn{D.Application{"bench"}, key(args), "value", value(args)},
      r => S.Finish{value(args)}}}
