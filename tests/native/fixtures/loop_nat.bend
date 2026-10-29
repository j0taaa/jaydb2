import Base
import ../../../native/effects.bend as Native

type State is Type:
  State{number: Nat, ready: Bool}

def finish(ok: Bool) -> Native.Iteracao<State>:
  match ok:
    case False{}:
      Native.Inconsistente{}
    case True{}:
      Native.Encerrar{[1]}

def step(state: State) -> Native.Iteracao<State>:
  match state:
    case State{n, False{}}:
      Native.Preparar{State{n, True{}}}
    case State{n, True{}}:
      finish(Nat.is_eq(n, Nat.add(Nat.pow(2n, 160n), 17n)))

def main() -> IO(Unit):
  do IO<Unit>:
    bytes : List<&2, U32> <- Native.read()
    Native.loop(State, step, State{Nat.add(Nat.pow(2n, 160n), 17n), False{}})
