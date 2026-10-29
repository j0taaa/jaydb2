import Base
import ../../../native/effects.bend as Native

def flag(value: Maybe<&2, F32>) -> U32:
  match value:
    case None{}:
      0
    case Some{f}:
      1

def valid(s: String) -> U32:
  flag(F32.read(s))

def pair(+s: String) -> List<&2, U32>:
  [valid(s), valid(s)]

def text(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case Con{x, tail}:
      SCon{Chr{x}, text(tail)}

def main() -> IO(Unit):
  do IO<Unit>:
    bytes : List<&2, U32> <- Native.read()
    Native.write(List.append(&2, U32, pair(text(bytes)), [
      valid(SCon{Chr{0}, "1"}),
      valid(SCon{Chr{55296}, "1"}),
      valid(SCon{Chr{1114112}, "1"}),
      valid(SCon{Chr{4294967295}, "1"}),
      valid(SCon{Chr{1114111}, "1"}),
      valid(SCon{Chr{8195}, "1"}),
      valid(SCon{Chr{1633}, SNil{}})
    ]))
