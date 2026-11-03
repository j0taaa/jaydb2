import Base
import ./Data.bend as D
import ./Semantics.bend as S

def start(ctx: D.Context, args: D.Value) -> S.Action:
  D.Context{id, kind} = ctx
  S.Finish{D.VText{id}}

def program() -> S.Program:
  S.Program{start}
