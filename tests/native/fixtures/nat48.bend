import Base
import ../../../native/effects.bend as Native

def pow2(n: Nat, +acc: Nat) -> Nat:
  match n:
    case 0n:
      acc
    case 1n+m:
      pow2(m, Nat.add(acc, acc))

def main() -> IO(Unit):
  do IO<Unit>:
    bytes : List<&2, U32> <- Native.read()
    Native.write([U32.from_nat(pow2(49n, 1n))])
