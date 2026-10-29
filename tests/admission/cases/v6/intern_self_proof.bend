import Base

def id(~p: Nat) -> Nat:
  p
def witness(~p: Nat) -> {id(p) == p : Nat}:
  {==}
def main() -> {id(id(1n)) == 1n : Nat}:
  witness(id(1n))
