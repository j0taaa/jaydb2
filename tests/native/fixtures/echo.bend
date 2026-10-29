import Base
import ../../../native/effects.bend as Native

def main() -> IO(Unit):
  do IO<Unit>:
    bytes : List<&2, U32> <- Native.read()
    Native.write(bytes)
