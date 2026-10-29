import Base

type Box<-A: Type> is Type:
  Box{value: A}
def f(~A: Type, ~p: A, n: Nat) -> Box<A>:
  match n:
    case Zero{}:
      Box{p}
    case Succ{x}:
      f(A, p, x)
law proof:
  for ~A: Type
  for ~p: A
  for n: Nat
  {f(A, p, n) == Box{p} : Box<A>}
def proof(A, p, n):
  match n:
    case Zero{}:
      {==}
    case Succ{x}:
      proof(A, p, x)
def main() -> {f(Nat, 4n, 2n) == Box{4n} : Box<Nat>}:
  proof(Nat, 4n, 2n)
