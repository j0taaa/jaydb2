# Staged as Client.bend. Both recurrence count and seed are runtime arguments.
import Base
import ./Data.bend as D
import ./Semantics.bend as S

def loop(n: Nat, x: U32) -> U32:
  match n:
    case 0n: x
    case 1n+k: loop(k, (x * 1664525 + 1013904223 : U32))

def compute(args: D.Value) -> U32:
  match args:
    case D.VList{D.VInt{0, n}, D.VList{D.VInt{0, seed}, D.VListEmpty{}}}:
      loop(U32.to_nat(n), seed)
    case _: 0

def respond(args: D.Value, r: S.Return) -> S.Action:
  match r:
    case S.Datum{D.Cell{v}}:
      S.Finish{D.VList{v, D.VList{D.VInt{0, compute(args)}, D.VListEmpty{}}}}
    case _: S.Refuse{D.VAbsent{}}

def start(ctx: D.Context, args: D.Value) -> S.Action:
  D.Context{id, kind} = ctx
  S.Access{D.ReadCell{D.Users{}, id, "credential"}, respond(args)}

def program() -> S.Program:
  S.Program{start}
