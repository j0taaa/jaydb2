# Serial dependent recurrence. Both iteration count and seed arrive at runtime.
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

def program() -> S.Program:
  S.Program{ctx => args => S.Finish{D.VInt{0, compute(args)}}}
