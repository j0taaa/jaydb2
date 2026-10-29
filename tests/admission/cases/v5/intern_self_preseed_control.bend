import Base

def id(~p: Nat) -> Nat:
  p
def seed() -> Nat:
  id(1n)
def main() -> Nat:
  id(id(1n))
