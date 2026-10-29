import Base
import ../../../native/effects.bend as Native

def count(n: Nat) -> U32:
  match n:
    case 0n:
      0
    case 1n+m:
      (count(m) + 1 : U32)

def pair(+n: Nat) -> List<&2, U32>:
  a b = count(n) count(n)
  [a, b]

def main() -> IO(Unit):
  do IO<Unit>:
    bytes : List<&2, U32> <- Native.read()
    Native.write(pair(13n))
