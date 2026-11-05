# Staged as Client.bend. Reads a row before returning runtime arguments.
import Base
import ./Data.bend as D
import ./Semantics.bend as S

def finish(args: D.Value, r: S.Return) -> S.Action:
  match args:
    case D.VInt{hi, lo}: S.Finish{D.VInt{hi, lo}}
    case D.VBool{b}: S.Finish{D.VInt{0, U32.from_nat(Nat.mul(16777216n, 16777216n))}}
    case _:
      match r:
        case S.Datum{D.Cell{v}}: S.Finish{v}
        case _: S.Refuse{D.VAbsent{}}

def start(ctx: D.Context, args: D.Value) -> S.Action:
  D.Context{id, kind} = ctx
  S.Access{D.ReadCell{D.Users{}, id, "credential"}, finish(args)}

def program() -> S.Program:
  S.Program{start}
