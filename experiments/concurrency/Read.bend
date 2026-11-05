# Staged as Client.bend. Reads an actual row before returning a runtime-sized sum.
import Base
import ./Data.bend as D
import ./Semantics.bend as S

def sum(n: U32, acc: U32) -> U32:
  if n == 0:
    acc
  else:
    sum((n - 1 : U32), (acc + 1 : U32))

def finish(args: D.Value, r: S.Return) -> S.Action:
  match args:
    case D.VInt{hi, lo}: S.Finish{D.VInt{0, sum(lo, 0)}}
    case D.VBool{b}: S.Finish{D.VText{String.from_nat(Nat.mul(16777216n, 16777216n))}}
    case _:
      match r:
        case S.Datum{D.Cell{v}}: S.Finish{v}
        case _: S.Refuse{D.VAbsent{}}

def start(ctx: D.Context, args: D.Value) -> S.Action:
  D.Context{id, kind} = ctx
  S.Access{D.ReadCell{D.Users{}, id, "credential"}, finish(args)}

def program() -> S.Program:
  S.Program{start}
