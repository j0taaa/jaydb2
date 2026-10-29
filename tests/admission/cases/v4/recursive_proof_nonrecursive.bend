import Base

def f(~p: Nat, n: Nat) -> Nat:
  match n:
    case Zero{}:
      p
    case Succ{x}:
      p
law proof:
  for ~p: Nat
  for n: Nat
  {f(p, n) == p : Nat}
def proof(p, n):
  match n:
    case Zero{}:
      {==}
    case Succ{x}:
      {==}
def main() -> {f(3n, 2n) == 3n : Nat}:
  proof(3n, 2n)
