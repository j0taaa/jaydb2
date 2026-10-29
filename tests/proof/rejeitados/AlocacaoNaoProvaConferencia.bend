import Base
import ../../../contrato/Interface.bend as I
import ../../../contrato/LAWS.bend as Leis

law falso:
  for -a: I.Ambiente
  for -k: String
  for -x: I.Cenario
  for -t: Nat
  for -pos: Nat
  for -n: Nat
  for alocou: I.Acontece(a, k, x, t, I.AlocouCampo{pos, n})
  Leis.Regra2(I.AlocouCampo{pos, n}, a, k, x, t)
def falso(a, k, x, t, pos, n, alocou):
  alocou
