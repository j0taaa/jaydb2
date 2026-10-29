import Base
import ../../../../contrato/Interface.bend as I
import ../../../../contrato/Recursos.bend as X

# Um evento declarado nao demonstra, sozinho, sua medicao real.
law falso:
  for -a: I.Ambiente
  for -k: String
  for -x: I.Cenario
  for -u: Nat
  for -etapa: X.Etapa
  for -n: Nat
  for mediu: I.Acontece(a, k, x, u, I.Mediu{X.Medicao{X.Tempo{etapa}, n}})
  I.MedicaoReal(a, k, x, u, X.Medicao{X.Tempo{etapa}, n})
def falso(a, k, x, u, etapa, n, mediu):
  mediu
