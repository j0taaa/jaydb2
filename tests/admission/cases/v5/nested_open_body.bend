import Base

def f(~p: Nat, n: Nat) -> Nat:
  match n:
    case Zero{}:
      p
    case Succ{x}:
      f(p, x)
def wrap(~p: Nat, n: Nat) -> Nat:
  f(p, n)
law proof:
  for ~p: Nat
  for n: Nat
  {wrap(p, n) == p : Nat}
def proof(p, n):
  match n:
    case Zero{}:
      {==}
    case Succ{x}:
      proof(p, x)
def main() -> {wrap(5n, 2n) == 5n : Nat}:
  proof(5n, 2n)
