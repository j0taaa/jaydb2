# Pure machine adapter to the runtime loop: no repeated accesses.
import Base
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Semantics.bend as S
import ./Core.bend as N
import ./Transport.bend as T
import ./Gate.bend as Gate

type StateExecution is Type:
  StateExecution{initial: D.State, machine: N.Machine}

type Iteration is Type:
  Continue{state: StateExecution}
  Prepare{state: StateExecution}
  FinishOutput{bytes: List<&2, U32>}
  Inconsistent{}

def start(program: S.Program, context: D.Context, arguments: D.Value,
  +initial: D.State) -> StateExecution:
  StateExecution{initial, N.start(program, context, arguments, initial)}

def packet_ready(bytes: Maybe<&2, List<&2, U32>>) -> Iteration:
  match bytes:
    case None{}:
      Inconsistent{}
    case Some{bs}:
      FinishOutput{Con{1, bs}}

def state_encoded(state: Maybe<&2, List<&2, U32>>,
  response: List<&2, U32>) -> Iteration:
  match state:
    case None{}:
      Inconsistent{}
    case Some{bs}:
      packet_ready(T.join(bs, response))

# The host obeys this sum; response status is inspected only here in Bend.
type Decision is Data:
  Commit{root: D.State, bytes: List<&2, U32>}
  Keep{bytes: List<&2, U32>}

def decision(conclusion: N.Conclusion) -> Decision:
  match conclusion:
    case N.Conclusion{state, S.Response{S.Success{}, value}, bytes}:
      Commit{state, bytes}
    case N.Conclusion{state, S.Response{status, value}, bytes}:
      Keep{bytes}

# Private ABI: 1 || frame(root) || response, or 0 || response.
def encode_decision(d: Decision) -> Iteration:
  match d:
    case Commit{state, bytes}: state_encoded(P.encode(D.state_value(state)), bytes)
    case Keep{bytes}: FinishOutput{Con{0, bytes}}

def conclude(conclusion: N.Conclusion) -> Iteration:
  encode_decision(decision(conclusion))

def result(conclusion: Maybe<&2, N.Conclusion>) -> Iteration:
  match conclusion:
    case None{}: Inconsistent{}
    case Some{c}: conclude(c)

def prepared(prepared: Maybe<&2, N.Prepared>, initial: D.State) -> Iteration:
  result(Gate.conclude(prepared, initial))

def after_step(machine: N.Machine, initial: D.State) -> Iteration:
  match machine:
    case N.Running{w, a, ts}:
      Continue{StateExecution{initial, N.Running{w, a, ts}}}
    case N.Stopped{w, ts, r}:
      Prepare{StateExecution{initial, N.Stopped{w, ts, r}}}

def advance(state: StateExecution, configuration: S.Configuration) -> Iteration:
  match state:
    case StateExecution{initial, N.Running{w, action, events}}:
      after_step(N.advance(N.Running{w, action, events}, S.schema(configuration)), initial)
    case StateExecution{initial, N.Stopped{w, events, response}}:
      result(Gate.finish(S.Final{w, events, response}, configuration, initial))

law refusal_emits_keep:
  for -state: D.State
  for -value: D.Value
  for -bytes: List<&2, U32>
  {conclude(N.Conclusion{state, S.Response{S.Refusal{}, value}, bytes}) ==
    FinishOutput{Con{0, bytes}} : Iteration}
def refusal_emits_keep(state, value, bytes):
  {==}
