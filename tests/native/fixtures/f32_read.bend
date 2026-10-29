import Base
import ../../../native/effects.bend as Native

def text(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case Con{x, tail}:
      SCon{Chr{x}, text(tail)}

def number(x: Maybe<&2, F32>) -> List<&2, U32>:
  match x:
    case None{}:
      [0]
    case Some{f}:
      +bits = F32.bits(f)
      [1, U32.and(bits, 255), U32.and(U32.div(bits, 256), 255),
       U32.and(U32.div(bits, 65536), 255), U32.div(bits, 16777216)]

def main() -> IO(Unit):
  do IO<Unit>:
    bytes : List<&2, U32> <- Native.read()
    Native.write(number(F32.read(text(bytes))))
