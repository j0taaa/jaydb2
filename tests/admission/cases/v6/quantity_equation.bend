import Base

def identity(~a: Quant, ~A: Kind(a), x: A) -> A:
  x
law proof:
  for ~a: Quant
  for ~A: Kind(a)
  for -x: A
  {identity(a, A, x) == x : A}
def proof(a, A, x):
  {==}
def main() -> {identity(&2, Nat, 4n) == 4n : Nat}:
  proof(&2, Nat, 4n)
