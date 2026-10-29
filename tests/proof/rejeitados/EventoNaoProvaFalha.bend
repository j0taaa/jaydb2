import Base
import ../../../contrato/Interface.bend as I
import ../../../contrato/Recursos.bend as X

law falso:
  for -a: I.Ambiente
  for -k: String
  for -x: I.Cenario
  for -t: Nat
  for -etapa: X.Etapa
  for -id: String
  for -fatal: Bool
  for falhou: I.Acontece(a, k, x, t, I.FalhouAmbiente{etapa, id, fatal})
  I.FalhaReal(a, k, x, t, etapa, id, fatal)
def falso(a, k, x, t, etapa, id, fatal, falhou):
  falhou
