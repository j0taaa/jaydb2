import Base

def f(~p: Nat, n: Nat) -> Nat:
  match n:
    case Zero{}:
      p
    case Succ{x}:
      f(p, x)
def domain(p: Nat) -> Type:
  @n: Nat -> {f(p, n) == f(p, n) : Nat}
def get(p: Nat) -> domain(p):
  n => {==}
def main() -> domain(3n):
  get(3n)
