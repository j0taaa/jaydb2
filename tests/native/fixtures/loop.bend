import Base
import ../../../native/effects.bend as Native

type TestState is Type:
  TestState{left: List<&2, U32>, rest: List<&2, U32>}

def step(state: TestState) -> Native.Iteracao<TestState>:
  match state:
    case TestState{left, Nil{}}:
      Native.Encerrar{left}
    case TestState{left, Con{h, t}}:
      match h:
        case 0:
          Native.Preparar{TestState{left, t}}
        case 255:
          Native.Inconsistente{}
        case _:
          Native.Continuar{TestState{Con{h, left}, t}}

def main() -> IO(Unit):
  do IO<Unit>:
    input : List<&2, U32> <- Native.read()
    Native.loop(TestState, step, TestState{Nil{}, input})
