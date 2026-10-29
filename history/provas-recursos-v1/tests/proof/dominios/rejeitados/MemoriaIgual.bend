import Base

# Falso: trocar excesso estrito por >= rejeita igualdade que deveria caber.
law falso:
  for +valor: Nat
  {Nat.is_ge(valor, valor) == Nat.is_gt(valor, valor) : Bool}
def falso(valor):
  {==}
