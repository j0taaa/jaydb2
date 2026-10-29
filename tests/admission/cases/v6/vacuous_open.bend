import Base

type Void is Type:
def rec(~A: Type, ~p: A, n: Nat) -> A:
  match n:
    case Zero{}:
      p
    case Succ{x}:
      rec(A, p, x)
def empty(~p: Void, n: Nat) -> Void:
  rec(Void, p, n)
def local_false(~p: {0n == 1n : Nat}) -> {0n == 1n : Nat}:
  p
def main() -> Nat:
  1n
