import Base
import ../../../native/effects.bend as Native

def count(xs: List<&2, U32>, +power: U32, value: U32) -> U32:
  match xs:
    case Nil{}:
      value
    case Con{x, rest}:
      count(rest, U32.mul(power, 256), U32.add(value, U32.mul(x, power)))

def depth(n: Nat) -> U32:
  match n:
    case 0n:
      0
    case 1n+k:
      U32.add(depth(k), 1)

def main() -> IO(Unit):
  do IO<Unit>:
    bytes : List<&2, U32> <- Native.read()
    Native.write([U32.and(depth(U32.to_nat(count(bytes, 1, 0))), 255)])
