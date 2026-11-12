# Pure machine adapter to the runtime loop: no repeated accesses.
import Base
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Semantics.bend as S
import ../contract/Requirements.bend as R
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

# Carry the encoding used for the state-size check to the actual Commit.
# Non-success responses still produce Keep, and framing failure is unchanged.
def response_packet(framed: Maybe<&2, List<&2, U32>>, response: S.Response,
  encoded: Maybe<&2, List<&2, U32>>) -> Iteration:
  match framed response:
    case None{} _: Inconsistent{}
    case Some{bytes} S.Response{S.Success{}, value}: state_encoded(encoded, bytes)
    case Some{bytes} S.Response{status, value}: FinishOutput{Con{0, bytes}}

def finish_encoded(+encoded: Maybe<&2, List<&2, U32>>, value: D.Value,
  c: S.Configuration, w: D.State) -> Iteration:
  +response = R.finalize_success_encoded(value, c, w, encoded)
  response_packet(P.frame(S.response_value(response)), response, encoded)

def finish(proposal: S.Response, c: S.Configuration, +w: D.State,
  events: List<&2, S.OperationEvent>, initial: D.State) -> Iteration:
  match proposal:
    case S.Response{S.Success{}, value}:
      finish_encoded(P.encode(D.state_value(w)), value, c, w)
    case other:
      prepared(N.prepare(N.Stopped{w, events, other}, c), initial)

law response_packet_equals_prepared:
  for +framed: Maybe<&2, List<&2, U32>>
  for response: S.Response
  for +w: D.State
  for events: List<&2, S.OperationEvent>
  for initial: D.State
  {response_packet(framed, response, P.encode(D.state_value(w))) ==
    prepared(N.prepare_bytes(framed, w, events, response), initial) : Iteration}
def response_packet_equals_prepared(framed, response, w, events, initial):
  match framed response:
    case None{} _: {==}
    case Some{bytes} S.Response{S.Success{}, value}: {==}
    case Some{bytes} S.Response{S.Refusal{}, value}: {==}
    case Some{bytes} S.Response{S.Input{}, value}: {==}
    case Some{bytes} S.Response{S.Authentication{}, value}: {==}
    case Some{bytes} S.Response{S.Certificate{}, value}: {==}
    case Some{bytes} S.Response{S.DataError{}, value}: {==}
    case Some{bytes} S.Response{S.Limit{}, value}: {==}
    case Some{bytes} S.Response{S.Failure{}, value}: {==}

# Exact equality includes invalid encodings, structural/data/limit denials,
# response framing failure, Keep and equal-root successful Commit.
law finish_equals_reference:
  for +proposal: S.Response
  for +c: S.Configuration
  for +w: D.State
  for +events: List<&2, S.OperationEvent>
  for +initial: D.State
  {finish(proposal, c, w, events, initial) ==
    prepared(N.prepare(N.Stopped{w, events, proposal}, c), initial) : Iteration}
def finish_equals_reference(proposal, c, w, events, initial):
  match proposal:
    case S.Response{S.Success{}, +value}:
      match c:
        case S.Configuration{+schema, +laws, +limits, +environment}:
          +configuration = S.Configuration{schema, laws, limits, environment}
          +response = R.finalize_success_encoded(value, configuration, w, P.encode(D.state_value(w)))
          response_packet_equals_prepared(P.frame(S.response_value(response)), response, w, events, initial)
    case S.Response{S.Refusal{}, value}: {==}
    case S.Response{S.Input{}, value}: {==}
    case S.Response{S.Authentication{}, value}: {==}
    case S.Response{S.Certificate{}, value}: {==}
    case S.Response{S.DataError{}, value}: {==}
    case S.Response{S.Limit{}, value}: {==}
    case S.Response{S.Failure{}, value}: {==}

def advance(state: StateExecution, configuration: S.Configuration) -> Iteration:
  match state:
    case StateExecution{initial, N.Running{w, action, events}}:
      after_step(N.advance(N.Running{w, action, events}, S.schema(configuration)), initial)
    case StateExecution{initial, N.Stopped{w, events, response}}:
      finish(response, configuration, w, events, initial)

law refusal_emits_keep:
  for -state: D.State
  for -value: D.Value
  for -bytes: List<&2, U32>
  {conclude(N.Conclusion{state, S.Response{S.Refusal{}, value}, bytes}) ==
    FinishOutput{Con{0, bytes}} : Iteration}
def refusal_emits_keep(state, value, bytes):
  {==}
