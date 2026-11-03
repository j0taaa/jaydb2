import Base
import ./Data.bend as D
import ./Semantics.bend as S

def sum(xs: List<U32>, acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      sum(t, (acc + h : U32))

def program() -> S.Program:
  S.Program{ctx => args => S.Finish{D.VInt{0, sum([1, 2, 3], 0)}}}
