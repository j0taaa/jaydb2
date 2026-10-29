import Base

def f(~p: Nat, n: Nat) -> Nat:
  match n:
    case Zero{}:
      p
    case Succ{x}:
      f(p, x)
def proof(p: Nat, n: Nat) -> {f(p, n) == p : Nat}:
  match n:
    case Zero{}:
      {==}
    case Succ{x}:
      proof(p, x)
def main(n: Nat) -> {f(3n, n) == 3n : Nat}:
  proof(3n, n)
