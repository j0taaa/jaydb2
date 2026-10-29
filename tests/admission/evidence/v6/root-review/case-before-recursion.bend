import Base

def f(~p: Nat, n: Nat) -> Nat:
  match n:
    case Zero{}: p
    case Succ{x}: f(p, x)
def helper(b: Bool,p: Nat,n: Nat) -> {f(p,n) == p : Nat}:
  match b:
    case False{}:
      match n:
        case Zero{}: {==}
        case Succ{x}: helper(b,p,x)
    case True{}:
      match n:
        case Zero{}: {==}
        case Succ{x}: helper(b,p,x)
def main(b: Bool,n: Nat) -> {f(3n,n) == 3n : Nat}:
  helper(b,3n,n)
