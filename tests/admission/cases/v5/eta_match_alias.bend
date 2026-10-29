import Base

def step(n: Nat) -> Nat:
  match n:
    case Zero{}:
      2n
    case Succ{x}:
      x
def f(~g: Nat -> Nat, n: Nat) -> Nat:
  match n:
    case Zero{}:
      g(0n)
    case Succ{x}:
      f(g, x)
def d(~g: Nat -> Nat) -> Type:
  @n: Nat -> {f(g, n) == f(g, n) : Nat}
def first() -> d(step):
  n => {==}
def main() -> d(x => step(x)):
  first()
