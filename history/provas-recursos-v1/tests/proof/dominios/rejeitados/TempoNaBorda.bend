import Base

# Falso: no maximo fisico, saturar um prazo maior pode antecipar expiracao.
law falso:
  for +maximo: Nat
  {Nat.is_ge(maximo, Nat.min(1n+maximo, maximo)) ==
    Nat.is_ge(maximo, 1n+maximo) : Bool}
def falso(maximo):
  {==}
