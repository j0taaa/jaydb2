import Base
import ./Data.bend as D
import ./Semantics.bend as S

def count(xs: List<U32>, acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      count(t, (acc + h : U32))

def program() -> S.Program:
  S.Program{c => a => S.Refuse{D.VInt{0, count([1, 2, 3], 0)}}}
