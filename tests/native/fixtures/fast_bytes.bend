import Base
import ../../../native/effects.bend as Native
import ../../../contract/Bytes.bend as B
import ../../../src/FastBytes.bend as F

def word(xs: List<&2, U32>, value: U32) -> U32:
  match xs:
    case Nil{}: value
    case Con{x, rest}: word(rest, U32.add(U32.mul(value, 256), x))

def natural(xs: List<&2, U32>, value: Nat) -> Nat:
  match xs:
    case Nil{}: value
    case Con{x, rest}: natural(rest, Nat.add(Nat.mul(value, 256n), U32.to_nat(x)))

def output(result: Maybe<&2, B.Number64>) -> List<&2, U32>:
  match result:
    case None{}: [0]
    case Some{B.Number64{high, low}}: 1 <> B.be64(high, low)

def run(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Con{0, rest}: output(F.nat64_checked(U32.to_nat(word(rest, 0))))
    case Con{1, rest}: output(F.nat64(U32.to_nat(word(rest, 0))))
    case Con{2, Con{n, rest}}:
      output(F.advance(U32.to_nat(n), Some{B.Number64{4294967295, 4294967294}}))
    case Con{3, rest}: output(F.nat64_checked(natural(rest, 0n)))
    case _: []

def main() -> IO(Unit):
  do IO<Unit>:
    bytes : List<&2, U32> <- Native.read()
    Native.write(run(bytes))
