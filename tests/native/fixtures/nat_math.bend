import Base
import ../../../native/effects.bend as Native

def main() -> IO(Unit):
  do IO<Unit>:
    bytes : List<&2, U32> <- Native.read()
    Native.write([
      U32.from_nat(Nat.mul(13n, 17n)),
      U32.pow(2, 7n),
      U32.shln(3, 5n),
      U32.from_nat(U32.log2(128)),
      U32.from_nat(Nat.div(200n, 17n)),
      U32.from_nat(Nat.mod(200n, 17n)),
      U32.and(U32.from_nat(Nat.add(256n, 4n)), 255)
    ])
