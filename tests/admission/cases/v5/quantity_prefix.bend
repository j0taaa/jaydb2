import Base

def identity(~a: Quant, ~A: Kind(a), x: A) -> A:
  x
def through(~a: Quant, ~A: Kind(a), x: A) -> A:
  identity(a, A, x)
def main() -> Nat:
  through(&2, Nat, 4n)
