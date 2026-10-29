import Base
import ../../../native/effects.bend as Native
import ./loop.bend as L

def capture(bytes: List<&2, U32>, state: L.TestState) -> Native.Iteracao<L.TestState>:
  Native.Encerrar{bytes}

def main() -> IO(Unit):
  do IO<Unit>:
    input : List<&2, U32> <- Native.read()
    Native.loop(L.TestState, capture(input), L.TestState{Nil{}, Nil{}})
