import Base
import ./Data.bend as D
import ./Semantics.bend as S

def program() -> S.Program:
  S.Program{ctx => args => S.Finish{args}}
