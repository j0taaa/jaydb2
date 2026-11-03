# Correspondence with the pure adapters used by the native controller/runtime.
# Does not assumes the host/ABI already implements these semantics.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Protocol.bend as P
import ../contract/Interface.bend as I
import ../contract/Logic.bend as L
import ../src/Core.bend as N
import ../src/Input.bend as E
import ../src/Execution.bend as X

def AuthenticationFaithful(result: E.Analysis, -r: P.Request, -s: D.State) -> Type:
  match result:
    case E.Received{state, request, context}:
      L.E<{state == s : D.State}, L.E<{request == r : P.Request},
        {D.authenticate(s, I.credential(r)) == Some{context} : Maybe<&2, D.Context>}>>
    case E.Rejected{S.Authentication{}}:
      {D.authenticate(s, I.credential(r)) == None{} : Maybe<&2, D.Context>}
    case _:
      Empty

def identity_faithful(q: Maybe<&2, D.Context>, -r: P.Request, -s: D.State,
  aut: {D.authenticate(s, I.credential(r)) == q : Maybe<&2, D.Context>}) ->
  AuthenticationFaithful(E.identity(q, s, r), r, s):
  match q:
    case None{}:
      aut
    case Some{c}:
      L.Both{{==}, L.Both{{==}, aut}}

law adapter_authenticates_state_and_credential_real:
  for +r: P.Request
  for +s: D.State
  AuthenticationFaithful(E.authenticate(Some{r}, s), r, s)
def adapter_authenticates_state_and_credential_real(r, s):
  match r:
    case P.Request{cred, cod, args, pi}:
      identity_faithful(D.authenticate(s, cred), P.Request{cred, cod, args, pi}, s, {==})

law input_received_has_identity_authenticates:
  for +r: P.Request
  for +s: D.State
  for -r2: P.Request
  for -s2: D.State
  for -ctx: D.Context
  for received: {E.authenticate(Some{r}, s) == E.Received{s2, r2, ctx} : E.Analysis}
  L.E<{s2 == s : D.State}, L.E<{r2 == r : P.Request},
    {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>}>>
def input_received_has_identity_authenticates(r, s, r2, s2, ctx, received):
  %received : AuthenticationFaithful(_, r, s)
  adapter_authenticates_state_and_credential_real(r, s)

law adapter_starts_machine_correct:
  for -p: S.Program
  for -ctx: D.Context
  for -args: D.Value
  for -s: D.State
  {X.start(p, ctx, args, s) ==
    X.StateExecution{s, N.Running{s, S.start(p, ctx, args), Nil{}}} : X.StateExecution}
def adapter_starts_machine_correct(p, ctx, args, s):
  {==}

def snapshot_of_iteration(i: X.Iteration) -> Maybe<&2, S.Trace>:
  match i:
    case X.Continue{X.StateExecution{s, m}}:
      Some{N.snapshot(m)}
    case X.Prepare{X.StateExecution{s, m}}:
      Some{N.snapshot(m)}
    case _:
      None{}

law adapter_preserves_machine_after_step:
  for m: N.Machine
  for -s: D.State
  {snapshot_of_iteration(X.after_step(m, s)) == Some{N.snapshot(m)} : Maybe<&2, S.Trace>}
def adapter_preserves_machine_after_step(m, s):
  match m:
    case N.Running{w, a, ts}:
      {==}
    case N.Stopped{w, ts, r}:
      {==}

law adapter_in_progress_advances_exactly_one_action:
  for -initial: D.State
  for -w: D.State
  for -action: S.Action
  for -ts: List<&2, S.OperationEvent>
  for -c: S.Configuration
  {X.advance(X.StateExecution{initial, N.Running{w, action, ts}}, c) ==
    X.after_step(N.advance(N.Running{w, action, ts}, S.schema(c)), initial) : X.Iteration}
def adapter_in_progress_advances_exactly_one_action(initial, w, action, ts, c):
  {==}

law adapter_stopped_only_prepares_and_concludes:
  for -initial: D.State
  for -w: D.State
  for -ts: List<&2, S.OperationEvent>
  for -r: S.Response
  for -c: S.Configuration
  {X.advance(X.StateExecution{initial, N.Stopped{w, ts, r}}, c) ==
    X.prepared(N.prepare(N.Stopped{w, ts, r}, c), initial) : X.Iteration}
def adapter_stopped_only_prepares_and_concludes(initial, w, ts, r, c):
  {==}

# The private zero marker prevents the controller from publishing even an
# identical copy of the old state on refusal/error. No state is serialized.
def SignalWithoutPublication(status: S.Status, -state: D.State,
  -value: D.Value, -bytes: List<&2, U32>) -> Type:
  match status:
    case S.Success{}:
      Unit
    case _:
      {X.conclude(N.Conclusion{state, S.Response{status, value}, bytes}) ==
        X.FinishOutput{Con{0, bytes}} : X.Iteration}

law all_outcome_without_success_emits_only_response:
  for status: S.Status
  for -state: D.State
  for -value: D.Value
  for -bytes: List<&2, U32>
  SignalWithoutPublication(status, state, value, bytes)
def all_outcome_without_success_emits_only_response(status, state, value, bytes):
  match status:
    case S.Success{}:
      Unit{}
    case S.Refusal{}:
      {==}
    case S.Input{}:
      {==}
    case S.Authentication{}:
      {==}
    case S.Certificate{}:
      {==}
    case S.DataError{}:
      {==}
    case S.Limit{}:
      {==}
    case S.Failure{}:
      {==}

def requests_publication(i: X.Iteration) -> Bool:
  match i:
    case X.FinishOutput{Con{flag, bs}}:
      U32.is_eq(flag, 1)
    case _:
      False{}

law all_command_of_publication_derive_of_success:
  for status: S.Status
  for -state: D.State
  for -value: D.Value
  for -bytes: List<&2, U32>
  for command: {requests_publication(X.conclude(N.Conclusion{state, S.Response{status, value}, bytes})) == True{} : Bool}
  {S.is_success(status) == True{} : Bool}
def all_command_of_publication_derive_of_success(status, state, value, bytes, command):
  match status:
    case S.Success{}:
      {==}
    case S.Refusal{}:
      command
    case S.Input{}:
      command
    case S.Authentication{}:
      command
    case S.Certificate{}:
      command
    case S.DataError{}:
      command
    case S.Limit{}:
      command
    case S.Failure{}:
      command
