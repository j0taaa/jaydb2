import Base

def ignore(-n: Nat) -> Nat:
  1n
def inner(~p: Nat) -> Nat:
  p
def witness(-n: Nat) -> {inner(1n) == 1n : Nat}:
  {==}
def main() -> {1n == 1n : Nat}:
  witness(2n)
