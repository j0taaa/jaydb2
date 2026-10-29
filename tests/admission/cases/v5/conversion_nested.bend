import Base

def ignore(-n: Nat) -> Nat:
  1n
def inner(~p: Nat) -> Nat:
  p
def outer(~p: Nat) -> Nat:
  inner(p)
def witness(-n: Nat) -> {outer(inner(ignore(n))) == 1n : Nat}:
  {==}
def main() -> {1n == 1n : Nat}:
  witness(3n)
