import Base

def f(~p: Nat, n: Nat) -> Nat:
  match n:
    case Zero{}:
      p
    case Succ{x}:
      f(p, x)
def domain(p: Nat) -> Type:
  @n: Nat -> {f(p, n) == f(p, n) : Nat}
def reflexive(p: Nat) -> domain(p):
  n => {==}
def main(n: Nat) -> {f(3n, n) == f(3n, n) : Nat}:
  reflexive(3n, n)
