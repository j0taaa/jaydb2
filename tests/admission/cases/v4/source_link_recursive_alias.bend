import Base

def f(~p: Nat, n: Nat) -> Nat:
  match n:
    case Zero{}:
      p
    case Succ{x}:
      f(p, x)
def d1(~p: Nat) -> Type:
  @n: Nat -> {f(p, n) == f(p, n) : Nat}
def main() -> d1(3n):
  n => {==}
