# Positive instance with THREE propositional laws and an actual read.
# The certificate is universal over s; no law is a Boolean test.
import Base
import ../../contract/Data.bend as D
import ../../contract/Semantics.bend as S
import ../../contract/Requirements.bend as R
import ../../contract/Interface.bend as I
import ../../contract/Logic.bend as L
import ../../src/Core.bend as N
import ../../proof/Safety.bend as G
import ../../proof/Preparation.bend as P
import ../../proof/Machine.bend as M
import ../../proof/Publication.bend as U
import ../../proof/Foundations.bend as F
import ../../contract/Protocol.bend as Wire
import ../../src/Execution.bend as X
import ../../src/Input.bend as E
import ../../proof/Adapters.bend as A

def context() -> D.Context:
  D.Context{"b", "person"}

def arguments() -> D.Value:
  D.VText{"exact argument"}

def code() -> String:
  "test program: count users and finish"

def operation() -> D.Operation:
  D.CountRows{D.Users{}}

def trace(s: D.State) -> List<&2, S.OperationEvent>:
  D.State{ts, us} = s
  [S.OperationEvent{operation(), S.Reading{D.Count{List.length(&2, D.Row, us)}}}]

def state_unchanged(h: S.Situation) -> Type:
  match h:
    case S.Stable{s}:
      Unit
    case S.Executing{s, ctx, cod, args, w, ts}:
      {w == s : D.State}
    case S.Closed{s, ctx, cod, args, w, ts, r}:
      {w == s : D.State}

def only_to_reading_declared(h: S.Situation) -> Type:
  match h:
    case S.Stable{s}:
      Unit
    case S.Executing{s, ctx, cod, args, w, ts}:
      L.Disjunction<{ts == Nil{} : List<&2, S.OperationEvent>}, {ts == trace(s) : List<&2, S.OperationEvent>}>
    case S.Closed{s, ctx, cod, args, w, ts, r}:
      L.Disjunction<{ts == Nil{} : List<&2, S.OperationEvent>}, {ts == trace(s) : List<&2, S.OperationEvent>}>

def origin_fixed(h: S.Situation) -> Type:
  match h:
    case S.Stable{s}:
      Unit
    case S.Executing{s, ctx, cod, args, w, ts}:
      L.E<{ctx == context() : D.Context}, L.E<{cod == code() : String}, {args == arguments() : D.Value}>>
    case S.Closed{s, ctx, cod, args, w, ts, r}:
      L.E<{ctx == context() : D.Context}, L.E<{cod == code() : String}, {args == arguments() : D.Value}>>

def configuration() -> S.Configuration:
  S.Configuration{D.Schema{Nil{}},
    S.MoreOneLaw{state_unchanged, S.MoreOneLaw{only_to_reading_declared,
      S.MoreOneLaw{origin_fixed, S.NoneLaw{}}}},
    S.Limits{1024n, 1024n, 256n}, "Bend-2.0.39-tests"}

def program() -> S.Program:
  S.Program{ctx => args => S.Access{operation(), return_value => S.Finish{D.VAbsent{}}}}

def user(+id: String, cred: String) -> D.Row:
  D.Row{id, [D.Field{"credential", D.VText{cred}}, D.Field{"id", D.VText{id}},
    D.Field{"kind", D.VText{"person"}}]}

def initial() -> D.State:
  D.State{Nil{}, [user("a", "first"), user("b", "second")]}

def laws_executing(-s: D.State, -ts: List<&2, S.OperationEvent>,
  reading: L.Disjunction<{ts == Nil{} : List<&2, S.OperationEvent>}, {ts == trace(s) : List<&2, S.OperationEvent>}>) ->
  S.Satisfies(configuration(), S.Executing{s, context(), code(), arguments(), s, ts}):
  L.Both{{==}, L.Both{reading, L.Both{L.Both{{==}, L.Both{{==}, {==}}}, Unit{}}}}

def laws_closed(-s: D.State, -ts: List<&2, S.OperationEvent>, -r: S.Response,
  reading: L.Disjunction<{ts == Nil{} : List<&2, S.OperationEvent>}, {ts == trace(s) : List<&2, S.OperationEvent>}>) ->
  S.Satisfies(configuration(), S.Closed{s, context(), code(), arguments(), s, ts, r}):
  L.Both{{==}, L.Both{reading, L.Both{L.Both{{==}, L.Both{{==}, {==}}}, Unit{}}}}

def prefix_zero(-s: D.State) -> R.SafetyPrefix(configuration(), s,
  context(), code(), arguments(), s, Nil{}):
  L.Both{laws_executing(s, Nil{}, L.Left{{==}}),
    laws_closed(s, Nil{}, S.response_error(S.Failure{}), L.Left{{==}})}

def prefix_read(-s: D.State) -> R.SafetyPrefix(configuration(), s,
  context(), code(), arguments(), s, trace(s)):
  L.Both{laws_executing(s, trace(s), L.Right{{==}}),
    laws_closed(s, trace(s), S.response_error(S.Failure{}), L.Right{{==}})}

def publication_unchanged(r: S.Response, -s: D.State,
  valid: R.Valid(configuration(), s)) -> R.PublicationValid(r, configuration(), s):
  match r:
    case S.Response{S.Success{}, v}:
      valid
    case S.Response{S.Refusal{}, v}:
      Unit{}
    case S.Response{S.Input{}, v}:
      Unit{}
    case S.Response{S.Authentication{}, v}:
      Unit{}
    case S.Response{S.Certificate{}, v}:
      Unit{}
    case S.Response{S.DataError{}, v}:
      Unit{}
    case S.Response{S.Limit{}, v}:
      Unit{}
    case S.Response{S.Failure{}, v}:
      Unit{}

law certificate:
  R.Certifies(configuration(), code(), program(), context(), arguments())
def certificate(s, valid, identity, n):
  match s n:
    case D.State{ts, us} 0n:
      prefix_zero(D.State{ts, us})
    case D.State{ts, us} 1n+m:
      match m:
        case 0n:
          prefix_read(D.State{ts, us})
        case 1n+k:
          %Equal.sym(S.Trace,
            S.resume_execution_trace(k, S.Stopped{D.State{ts, us}, S.Response{S.Success{}, D.VAbsent{}}},
              D.Schema{Nil{}}, trace(D.State{ts, us})),
            S.Final{D.State{ts, us}, trace(D.State{ts, us}), S.Response{S.Success{}, D.VAbsent{}}},
            M.reference_stopped(k, D.State{ts, us}, trace(D.State{ts, us}), S.Response{S.Success{}, D.VAbsent{}}, D.Schema{Nil{}})) :
              R.SafetyTrace(_, configuration(), D.State{ts, us}, context(), code(), arguments())
          L.Both{prefix_read(D.State{ts, us}),
            L.Both{laws_closed(D.State{ts, us}, trace(D.State{ts, us}),
              R.finalize(S.Response{S.Success{}, D.VAbsent{}}, configuration(), D.State{ts, us}), L.Right{{==}}),
              publication_unchanged(R.finalize(S.Response{S.Success{}, D.VAbsent{}}, configuration(), D.State{ts, us}),
                D.State{ts, us}, valid)}}

law terminates:
  I.ProgramTerminates(configuration(), program())
def terminates(s, ctx, args):
  match s:
    case D.State{+ts, +us}:
      (2n, D.State{ts, us}, trace(D.State{ts, us}), S.Response{S.Success{}, D.VAbsent{}}, {==})

law initial_valid:
  R.Valid(configuration(), initial())
def initial_valid():
  L.Both{{==}, L.Both{Unit{}, L.Both{Unit{}, L.Both{Unit{}, Unit{}}}}}

law context_real:
  {D.authenticate(initial(), "second") == Some{context()} : Maybe<&2, D.Context>}
def context_real():
  {==}

law safety_general_of_test:
  for n: Nat
  R.SafetyTrace(N.traverse(n, N.start(program(), context(), arguments(), initial()), S.schema(configuration())),
    configuration(), initial(), context(), code(), arguments())
def safety_general_of_test(n):
  G.certificate_covers_execution_authenticated(configuration(), code(), program(), context(), arguments(),
    certificate(), initial(), initial_valid(), "second", context_real(), n)

law publication_real_is_valid:
  R.Valid(configuration(), S.publish(S.Response{S.Success{}, D.VAbsent{}}, initial(), initial()))
def publication_real_is_valid():
  G.conclusion_certified_preserves_validity(S.Response{S.Success{}, D.VAbsent{}}, configuration(), code(),
    program(), context(), arguments(), certificate(), initial(), initial_valid(), "second", context_real(),
    2n, initial(), trace(initial()), S.Response{S.Success{}, D.VAbsent{}}, {==}, {==})

law interruption_later_of_reading:
  S.Satisfies(configuration(), S.Closed{initial(), context(), code(), arguments(),
    initial(), trace(initial()), S.response_error(S.Failure{})})
def interruption_later_of_reading():
  G.interruption_certified_preserves_all_as_laws(G.ByFailure{}, configuration(), code(), program(), context(), arguments(),
    certificate(), initial(), initial_valid(), "second", context_real(), 1n, S.Prefix{initial(), trace(initial())}, {==})

law size_and_payload_real:
  P.Preparable(S.limits(configuration()), R.finalize(S.Response{S.Success{}, D.VAbsent{}}, configuration(), initial()))
def size_and_payload_real():
  P.finalize_guarantees_payload_and_size(S.Response{S.Success{}, D.VAbsent{}}, configuration(), initial(), {==})

def response() -> S.Response:
  S.Response{S.Success{}, D.VAbsent{}}

def machine_final() -> N.Machine:
  N.Stopped{initial(), trace(initial()), response()}

def prepared() -> N.Prepared:
  N.Prepared{initial(), trace(initial()), response(),
    F.extract_or(List<&2, U32>, Wire.frame(S.response_value(response())), Nil{})}

law preparation_real_obtained:
  {N.prepare(machine_final(), configuration()) == Some{prepared()} : Maybe<&2, N.Prepared>}
def preparation_real_obtained():
  {==}

law preparation_real_faithful:
  P.Faithful(initial(), trace(initial()), R.finalize(response(), configuration(), initial()), prepared())
def preparation_real_faithful():
  P.prepare_preserves_response_state_events_and_bytes(machine_final(), configuration(), prepared(), preparation_real_obtained())

law cycle_real_of_preparation_and_publication_valid:
  R.Valid(configuration(), U.published(N.conclude(prepared(), initial())))
def cycle_real_of_preparation_and_publication_valid():
  U.conclusion_of_preparation_certified_and_is_valid(configuration(), code(), program(), context(), arguments(),
    certificate(), initial(), initial_valid(), "second", context_real(), 2n, initial(), trace(initial()),
    response(), {==}, prepared(), preparation_real_faithful())

def request() -> Wire.Request:
  Wire.Request{"second", code(), arguments(), "test certificate"}

law adapter_request_real:
  {E.authenticate(Some{request()}, initial()) == E.Received{initial(), request(), context()} : E.Analysis}
def adapter_request_real():
  {==}

law identity_of_adapter_negative_comes_of_arguments:
  L.E<{initial() == initial() : D.State}, L.E<{request() == request() : Wire.Request},
    {D.authenticate(initial(), I.credential(request())) == Some{context()} : Maybe<&2, D.Context>}>>
def identity_of_adapter_negative_comes_of_arguments():
  A.input_received_has_identity_authenticates(request(), initial(), request(), initial(), context(), adapter_request_real())

def first_iteration() -> X.Iteration:
  X.advance(X.start(program(), context(), arguments(), initial()), configuration())

def next(i: X.Iteration) -> X.Iteration:
  match i:
    case X.Continue{state}:
      X.advance(state, configuration())
    case X.Prepare{state}:
      X.advance(state, configuration())
    case X.FinishOutput{bytes}:
      X.FinishOutput{bytes}
    case X.Inconsistent{}:
      X.Inconsistent{}

law loop_first_step_contains_reading:
  {first_iteration() == X.Continue{X.StateExecution{initial(), N.Running{initial(), S.Finish{D.VAbsent{}}, trace(initial())}}} : X.Iteration}
def loop_first_step_contains_reading():
  {==}

law loop_second_step_requests_preparation:
  {next(first_iteration()) == X.Prepare{X.StateExecution{initial(), machine_final()}} : X.Iteration}
def loop_second_step_requests_preparation():
  {==}

law loop_third_step_prepares_and_concludes:
  {next(next(first_iteration())) == X.conclude(N.conclude(prepared(), initial())) : X.Iteration}
def loop_third_step_prepares_and_concludes():
  {==}
