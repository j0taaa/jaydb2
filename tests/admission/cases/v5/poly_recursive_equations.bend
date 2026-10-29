import Base

def f(~A: Type, ~p: A, n: Nat) -> A:
  match n:
    case Zero{}:
      p
    case Succ{x}:
      f(A, p, x)
law proof:
  for ~A: Type
  for ~p: A
  for n: Nat
  {f(A, p, n) == p : A}
def proof(A, p, n):
  match n:
    case Zero{}:
      {==}
    case Succ{x}:
      proof(A, p, x)
def main() -> {f(Nat, 7n, 2n) == 7n : Nat}:
  proof(Nat, 7n, 2n)
