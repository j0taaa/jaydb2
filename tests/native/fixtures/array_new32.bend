import Base
import ../../../native/effects.bend as Native

def first(a: Array<U32>) -> U32:
  match a:
    case ALeaf{x}:
      x
    case ANode{xs, ys}:
      first(xs)

def main() -> IO(Unit):
  do IO<Unit>:
    bytes : List<&2, U32> <- Native.read()
    Native.write([first(Array.new(U32, 32n, 7))])
