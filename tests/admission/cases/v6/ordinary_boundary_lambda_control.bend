import Base

def f(~p: Nat, n: Nat) -> Nat:
  p
def reflexive(p: Nat, n: Nat) -> {f(p, n) == f(p, n) : Nat}:
  {==}
def main(n: Nat) -> {f(3n, n) == f(3n, n) : Nat}:
  reflexive(3n, n)
