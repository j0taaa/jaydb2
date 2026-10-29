import Base
import ../../../native/effects.bend as Native

def sum(n: Nat, acc: U32) -> U32:
  match n:
    case 0n:
      acc
    case 1n+m:
      sum(m, (acc + 1 : U32))

def main() -> IO(Unit):
  do IO<Unit>:
    bytes : List<&2, U32> <- Native.read()
    Native.write([U32.and(sum(10000000n, 0), 255)])
