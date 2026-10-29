import Base
import ./Dados.bend as D
import ./Semantica.bend as S

def programa() -> S.Programa:
  S.Programa{ctx => args => S.Terminar{args}}
