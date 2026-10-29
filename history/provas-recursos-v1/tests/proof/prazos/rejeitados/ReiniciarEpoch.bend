import Base

# Estar exatamente no prazo original nao autoriza somar o orcamento a agora.
law falso:
  for +inicio: Nat
  for +orcamento: Nat
  {Nat.is_ge(Nat.add(inicio, 1n+orcamento),
    Nat.add(Nat.add(inicio, 1n+orcamento), 1n+orcamento)) == True{} : Bool}
def falso(inicio, orcamento):
  {==}
