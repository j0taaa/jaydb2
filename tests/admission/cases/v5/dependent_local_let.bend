import Base

def f(~p: Nat, n: Nat) -> Nat:
  match n:
    case Zero{}:
      p
    case Succ{x}:
      f(p, x)
def domain(p: Nat) -> Type:
  @n: Nat -> {f(p, n) == f(p, n) : Nat}
def make(~p: Nat) -> domain(p):
  local: domain(p) = n => {==}
  local
def main() -> domain(5n):
  make(5n)
