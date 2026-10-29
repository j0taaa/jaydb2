import Base
import ../../../native/effects.bend as Native

# Exercise runtime Nat limbs and a captured function, Array constructors, and
# F32/string bytes in one Book; general contract laws live in the proof gate.
def apply(f: Nat -> Nat, value: Nat) -> Nat:
  f(value)

def ascii(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{x}, tail}:
      Con{x, ascii(tail)}

def text(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case Con{x, tail}:
      SCon{Chr{x}, text(tail)}

def tower(n: Nat) -> Array<U32>:
  match n:
    case 0n:
      ALeaf{7}
    case 1n+m:
      ANode{tower(m), ALeaf{7}}

def depth(a: Array<U32>) -> U32:
  match a:
    case ALeaf{x}:
      0
    case ANode{xs, ys}:
      (1 + depth(xs) : U32)

def number(x: Maybe<&2, F32>) -> List<&2, U32>:
  match x:
    case None{}:
      [0]
    case Some{f}:
      +bits = F32.bits(f)
      [1, U32.and(bits, 255), U32.and(U32.div(bits, 256), 255),
       U32.and(U32.div(bits, 65536), 255), U32.div(bits, 16777216)]

def represent(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Con{0, Con{value, rest}}:
      ascii(Nat.show(apply(Nat.add(Nat.add(Nat.pow(2n, 129n), 1n)), U32.to_nat(value))))
    case Con{1, rest}:
      [depth(tower(32n))]
    case Con{2, rest}:
      number(F32.read(text(rest)))
    case _:
      Nil{}

def main() -> IO(Unit):
  do IO<Unit>:
    bytes : List<&2, U32> <- Native.read()
    Native.write(represent(bytes))
