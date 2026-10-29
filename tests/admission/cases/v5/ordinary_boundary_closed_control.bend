import Base

def f(~p: Nat, n: Nat) -> Nat:
  match n:
    case Zero{}:
      p
    case Succ{x}:
      f(p, x)
def reflexive(p: Nat, n: Nat) -> {f(p, n) == f(p, n) : Nat}:
  {==}
def main() -> {f(3n, 2n) == f(3n, 2n) : Nat}:
  reflexive(3n, 2n)
