import Base
import ../../../native/effects.bend as Native

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

def main() -> IO(Unit):
  do IO<Unit>:
    bytes : List<&2, U32> <- Native.read()
    Native.write([depth(tower(32n))])
