import Base

def folder(~f: Nat -> Nat -> Nat, xs: List<&2, Nat>, z: Nat) -> Nat:
  List.foldr(&2, Nat, Nat, f, xs, z)
def add(x: Nat, y: Nat) -> Nat:
  Nat.add(x, y)
def main() -> Nat:
  folder(add, [1n, 2n, 3n], 0n)
