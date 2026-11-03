import Base
import ../../../native/effects.bend as Native

type TestState is Type:
  TestState{left: List<&2, U32>, rest: List<&2, U32>}

def advance(state: TestState) -> Native.Iteration<(Unit -> TestState)>:
  match state:
    case TestState{left, Nil{}}:
      Native.FinishOutput{left}
    case TestState{left, Con{h, t}}:
      match h:
        case 0:
          Native.Prepare{u => TestState{left, t}}
        case 255:
          Native.Inconsistent{}
        case _:
          Native.Continue{u => TestState{Con{h, left}, t}}

def step(box: Unit -> TestState) -> Native.Iteration<(Unit -> TestState)>:
  advance(box(Unit{}))

def main() -> IO(Unit):
  do IO<Unit>:
    input : List<&2, U32> <- Native.read()
    Native.loop((Unit -> TestState), step, u => TestState{Nil{}, input})
