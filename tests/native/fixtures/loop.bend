import Base
import ../../../native/effects.bend as Native

type TestState is Type:
  TestState{left: List<&2, U32>, rest: List<&2, U32>}

def advance(state: TestState) -> Native.Iteracao<(Unit -> TestState)>:
  match state:
    case TestState{left, Nil{}}:
      Native.Encerrar{left}
    case TestState{left, Con{h, t}}:
      match h:
        case 0:
          Native.Preparar{u => TestState{left, t}}
        case 255:
          Native.Inconsistente{}
        case _:
          Native.Continuar{u => TestState{Con{h, left}, t}}

def step(box: Unit -> TestState) -> Native.Iteracao<(Unit -> TestState)>:
  advance(box(Unit{}))

def main() -> IO(Unit):
  do IO<Unit>:
    input : List<&2, U32> <- Native.read()
    Native.loop((Unit -> TestState), step, u => TestState{Nil{}, input})
