import Base
import ../../../native/effects.bend as Native
import ./loop.bend as L

def main() -> IO(Unit):
  do IO<Unit>:
    Unit <- Native.enter(1)
    input : List<&2, U32> <- Native.read()
    Native.loop(L.TestState, L.step, L.TestState{Nil{}, input})
