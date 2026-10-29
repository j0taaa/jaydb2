import Base
import ../../../native/effects.bend as Native

def ascii(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{x}, t}:
      Con{x, ascii(t)}

def main() -> IO(Unit):
  do IO<Unit>:
    bytes : List<&2, U32> <- Native.read()
    Native.write(ascii(F32.show(1.25)))
