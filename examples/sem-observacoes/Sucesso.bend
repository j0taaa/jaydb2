import Base
import ./Dados.bend as D
import ./Semantica.bend as S

def somar(xs: List<U32>, acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      somar(t, (acc + h : U32))

def programa() -> S.Programa:
  S.Programa{ctx => args => S.Terminar{D.VInt{0, somar([1, 2, 3], 0)}}}
