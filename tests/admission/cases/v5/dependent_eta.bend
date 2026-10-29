import Base

def family(n: Nat) -> Type:
  {n == n : Nat}
def witness(n: Nat) -> family(n):
  {==}
def apply(~P: Nat -> Type, ~p: @n: Nat -> P(n), n: Nat) -> P(n):
  p(n)
def outer(~P: Nat -> Type, ~p: @n: Nat -> P(n), n: Nat) -> P(n):
  apply(x => P(x), x => p(x), n)
def first() -> family(3n):
  apply(family, witness, 3n)
def main() -> family(3n):
  outer(family, witness, 3n)
