import Base

def id(~p: Nat) -> Nat:
  p
def main() -> Nat:
  id(id(1n))
