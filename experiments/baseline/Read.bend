import Base
import ./Data.bend as D
import ./Semantics.bend as S

def key(args: D.Value) -> String:
  match args:
    case D.VText{k}: k
    case _: "missing"

def respond(r: S.Return) -> S.Action:
  match r:
    case S.Datum{D.Cell{v}}: S.Finish{v}
    case _: S.Refuse{D.VAbsent{}}

def program() -> S.Program:
  S.Program{ctx => args =>
    S.Access{D.ReadCell{D.Application{"bench"}, key(args), "value"}, respond}}
