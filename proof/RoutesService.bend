# Deterministic protocol ending generation; not an alternative server.
import Base
import ./ProtocolService.bend as Q
import ./PrimitivesService.bend as M
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Protocol.bend as P
import ../contract/Resources.bend as X
import ../contract/Logic.bend as L
import ../src/Core.bend as N
import ../src/Input.bend as E
import ../contract/RequestFacts.bend as I
import ../src/Transport.bend as T
import ../src/ConfigurationCheck.bend as C

type Delivery is Data:
  Complete{next: Bool}
  Broken{prefix: List<&2, U32>}
  PendingDelivery{}

def later_delivery(closes: Bool, +state: D.State, next: Bool) -> List<&2, Q.Frame>:
  match closes next:
    case True{} _: [Q.Closed{}]
    case False{} True{}: [Q.Next{state, state}]
    case False{} False{}: Nil{}

def render_delivery(+state: D.State, bytes: List<&2, U32>, closes: Bool, delivery: Delivery) -> List<&2, Q.Frame>:
  match delivery:
    case Complete{next}: Con{Q.Delivered{bytes}, later_delivery(closes, state, next)}
    case Broken{prefix}: [Q.Interrupted{prefix}, Q.Closed{}]
    case PendingDelivery{}: Nil{}

def render_publication(response: S.Response, state: D.State) -> List<&2, Q.Frame>:
  match response:
    case S.Response{S.Success{}, v}: [Q.Published{state}]
    case _: Nil{}

def render_conclusion(conclusion: N.Conclusion, +closes: Bool, delivery: Delivery) -> List<&2, Q.Frame>:
  match conclusion:
    case N.Conclusion{+state, +response, +bytes}:
      Con{Q.Prepared{response, bytes},
        Q.concatenate(render_publication(response, state),
          Con{Q.Completed{response, state, closes}, render_delivery(state, bytes, closes, delivery)})}

def render_final(prepared: N.Prepared, initial: D.State, closes: Bool, delivery: Delivery) -> List<&2, Q.Frame>:
  render_conclusion(N.conclude(prepared, initial), closes, delivery)

# Error branches never pass through render_publication, even without valid state.
def render_error_framed(result: Maybe<&2, List<&2, U32>>, +response: S.Response,
  +initial: D.State, +closes: Bool, delivery: Delivery) -> List<&2, Q.Frame>:
  match result:
    case None{}: Nil{}
    case Some{+bytes}:
      Q.concatenate([Q.Prepared{response, bytes}, Q.Completed{response, initial, closes}],
        render_delivery(initial, bytes, closes, delivery))

def render_error(status: S.Status, initial: D.State, closes: Bool, delivery: Delivery) -> List<&2, Q.Frame>:
  +response = S.response_error(status)
  render_error_framed(P.frame(S.response_value(response)), response, initial, closes, delivery)

# Micro-operation sources; never arbitrary frames with publications.

type Micro is Data:
  Micro{input: List<&2, M.Primitive>, authentication: List<&2, M.Primitive>,
    execution: List<&2, M.Primitive>, output: List<&2, M.Primitive>}

def micro_input(m: Micro) -> List<&2, Q.Frame>:
  Micro{a, b, c, d} = m
  M.expand_primitives(a)
def micro_authentication(m: Micro) -> List<&2, Q.Frame>:
  Micro{a, b, c, d} = m
  M.expand_primitives(b)
def micro_execution(m: Micro) -> List<&2, Q.Frame>:
  Micro{a, b, c, d} = m
  M.expand_primitives(c)
def micro_output(m: Micro) -> List<&2, Q.Frame>:
  Micro{a, b, c, d} = m
  M.expand_primitives(d)

def render_received(m: Micro, +r: P.Request) -> List<&2, Q.Frame>:
  Q.concatenate(micro_input(m), [Q.Received{r}])
def render_authenticated(+m: Micro, +r: P.Request, ctx: D.Context) -> List<&2, Q.Frame>:
  Q.concatenate(render_received(m, r), Q.concatenate(micro_authentication(m), [Q.Authenticated{r, Some{ctx}}]))
def render_verified(m: Micro, +r: P.Request, +ctx: D.Context) -> List<&2, Q.Frame>:
  Q.concatenate(render_authenticated(m, r, ctx), [Q.Accepts{r, ctx}])
def render_started(+m: Micro, +r: P.Request, +ctx: D.Context) -> List<&2, Q.Frame>:
  Q.concatenate(render_verified(m, r, ctx), Q.concatenate(micro_execution(m), [Q.Started{r, ctx}]))
def render_execution(m: Micro, +r: P.Request, +ctx: D.Context, execution: List<&2, Q.FrameExec>) -> List<&2, Q.Frame>:
  Q.concatenate(render_started(m, r, ctx), Q.expand_exec(r, ctx, execution))

def frame_prepared(p: N.Prepared) -> Q.Frame:
  N.Prepared{w, ts, r, bs} = p
  Q.Prepared{r, bs}

# None of these phases can publish or conclude independently.
type PhaseBefore is Data:
  BeforeInput{}
  AfterReceive{request: P.Request}
  AfterAuthenticate{request: P.Request, context: D.Context}
  AfterVerify{request: P.Request, context: D.Context}
  Executing{request: P.Request, context: D.Context, execution: List<&2, Q.FrameExec>}
  AfterPrepare{request: P.Request, context: D.Context, execution: List<&2, Q.FrameExec>, prepared: N.Prepared}

def render_phase(+m: Micro, phase: PhaseBefore) -> List<&2, Q.Frame>:
  match phase:
    case BeforeInput{}: micro_input(m)
    case AfterReceive{r}: render_received(m, r)
    case AfterAuthenticate{r, ctx}: render_authenticated(m, r, ctx)
    case AfterVerify{r, ctx}: render_verified(m, r, ctx)
    case Executing{r, ctx, exec}: render_execution(m, r, ctx, exec)
    case AfterPrepare{r, ctx, exec, p}:
      Q.concatenate(render_execution(m, r, ctx, exec), Q.concatenate(micro_output(m), [frame_prepared(p)]))

type ErrorInput is Data:
  Input{}
  Limit{}
def status_input(error: ErrorInput) -> S.Status:
  match error:
    case Input{}: S.Input{}
    case Limit{}: S.Limit{}

type Branch is Data:
  InitialOk{}
  InitialRefusal{status: S.Status}
  InitialFailure{accepts: Bool, stage: X.Stage, identifier: String, fatal: Bool}
  WithoutResponse{}
  InputRefusal{error: ErrorInput, closes: Bool, delivery: Delivery}
  AutRefusal{request: P.Request, delivery: Delivery}
  GateRefusal{request: P.Request, context: D.Context, delivery: Delivery}
  Executed{request: P.Request, context: D.Context,
    execution: List<&2, Q.FrameExec>, prepared: N.Prepared, delivery: Delivery}
  FailureBefore{phase: PhaseBefore, stage: X.Stage, identifier: String, fatal: Bool, delivery: Delivery}
  FatalAfterPublication{request: P.Request, context: D.Context,
    execution: List<&2, Q.FrameExec>, prepared: N.Prepared, stage: X.Stage, identifier: String}
  Pending{phase: PhaseBefore}
  InitialPending{proof_accepts: Bool}

def render_initial(result: Maybe<&2, List<&2, U32>>, +initial: D.State) -> List<&2, Q.Frame>:
  match result:
    case None{}: [Q.Encoded{D.state_value(initial), None{}}]
    case Some{+bs}: [Q.Encoded{D.state_value(initial), Some{bs}}, Q.Stored{initial, bs, initial}, Q.Initialized{initial}]

def render_failure_end(initial: D.State, fatal: Bool, delivery: Delivery) -> List<&2, Q.Frame>:
  match fatal:
    case True{}: [Q.Closed{}]
    case False{}: render_error(S.Failure{}, initial, False{}, delivery)
def render_failure(initial: D.State, stage: X.Stage, id: String, +fatal: Bool, delivery: Delivery) -> List<&2, Q.Frame>:
  Con{Q.Failed{stage, id, fatal}, render_failure_end(initial, fatal, delivery)}

def render_fatal_published(conclusion: N.Conclusion, stage: X.Stage, id: String) -> List<&2, Q.Frame>:
  match conclusion:
    case N.Conclusion{state, +r, bs}:
      Con{Q.Prepared{r, bs}, Q.concatenate(render_publication(r, state), [Q.Failed{stage, id, True{}}, Q.Closed{}])}

def prefix_initial(+m: Micro, accepts: Bool) -> List<&2, Q.Frame>:
  match accepts:
    case True{}: Con{Q.InitialAccepts{}, micro_output(m)}
    case False{}: Nil{}

def render_branch(+m: Micro, +initial: D.State, branch: Branch) -> List<&2, Q.Frame>:
  match branch:
    case InitialOk{}:
      Con{Q.InitialAccepts{}, Q.concatenate(micro_output(m), render_initial(P.encode(D.state_value(initial)), initial))}
    case InitialRefusal{s}: [Q.InitialRefused{s}]
    case InitialFailure{accepts, stage, id, fatal}:
      Q.concatenate(prefix_initial(m, accepts), [Q.Failed{stage, id, fatal}, Q.InitialRefused{S.Failure{}}])
    case WithoutResponse{}: [Q.Closed{}]
    case InputRefusal{error, closes, delivery}:
      Q.concatenate(micro_input(m), render_error(status_input(error), initial, closes, delivery))
    case AutRefusal{+r, delivery}:
      Q.concatenate(render_received(m, r), Q.concatenate(micro_authentication(m),
        Con{Q.Authenticated{r, None{}}, render_error(S.Authentication{}, initial, False{}, delivery)}))
    case GateRefusal{+r, +ctx, delivery}:
      Q.concatenate(render_authenticated(m, r, ctx), Con{Q.Rejected{r, ctx}, render_error(S.Certificate{}, initial, False{}, delivery)})
    case Executed{r, ctx, exec, p, delivery}:
      Q.concatenate(render_execution(m, r, ctx, exec), Q.concatenate(micro_output(m), render_final(p, initial, False{}, delivery)))
    case FailureBefore{phase, stage, id, fatal, delivery}:
      Q.concatenate(render_phase(m, phase), render_failure(initial, stage, id, fatal, delivery))
    case FatalAfterPublication{r, ctx, exec, p, stage, id}:
      Q.concatenate(render_execution(m, r, ctx, exec), Q.concatenate(micro_output(m), render_fatal_published(N.conclude(p, initial), stage, id)))
    case Pending{phase}: render_phase(m, phase)
    case InitialPending{accepts}: prefix_initial(m, accepts)

def render(m: Micro, +initial: D.State, branch: Branch) -> List<&2, Q.Frame>:
  Con{Q.Configured{}, render_branch(m, initial, branch)}


# Tool/process results; no field is a database law.
type Judgment is Data:
  Accepted{}
  Refused{}
  ErrorJudgment{identifier: String, fatal: Bool}
  PendingJudgment{}

type PointExec is Data:
  BeforeOfStart{}
  During{frames: List<&2, Q.FrameExec>}
  Prepared{frames: List<&2, Q.FrameExec>, prepared: N.Prepared}

type OutputExecution is Data:
  Finalized{frames: List<&2, Q.FrameExec>, prepared: N.Prepared}
  ErrorExecution{point: PointExec, stage: X.Stage, identifier: String, fatal: Bool}
  PendingExecution{point: PointExec}

# Host action result after the executor: cleanup and root exchange.
type Cleanup is Data:
  Clears{}
  ErrorCleanup{identifier: String, fatal: Bool}
  FatalAfterStore{stage: X.Stage, identifier: String}
  PendingCleanup{}

# IO/process failure appears only when its stage was actually reached.
type Preprocessing is Data:
  Normal{}
  FailureFraming{identifier: String, fatal: Bool}
  FailureDecode{identifier: String, fatal: Bool}
  FailureAuth{identifier: String, fatal: Bool}
  PendingFraming{}
  PendingDecode{}
  PendingAuth{}

type DataTools is Data:
  DataTools{judgment: Judgment, execution: OutputExecution, cleanup: Cleanup,
    delivery: Delivery, preprocessing: Preprocessing}

def preprocessing(d: DataTools) -> Preprocessing:
  DataTools{j, ex, li, en, pre} = d
  pre

def delivery_of(d: DataTools) -> Delivery:
  DataTools{j, ex, li, en, pre} = d
  en

def judgment_of(d: DataTools) -> Judgment:
  DataTools{j, ex, li, en, pre} = d
  j

def error_of_message(status: S.Status) -> ErrorInput:
  match status:
    case S.Limit{}: Limit{}
    case _: Input{}

def phase_of_error(point: PointExec, r: P.Request, ctx: D.Context) -> PhaseBefore:
  match point:
    case BeforeOfStart{}: AfterVerify{r, ctx}
    case During{frames}: Executing{r, ctx, frames}
    case Prepared{frames, prepared}: AfterPrepare{r, ctx, frames, prepared}

def decide_cleanup(r: P.Request, ctx: D.Context, frames: List<&2, Q.FrameExec>,
  prepared: N.Prepared, cleanup: Cleanup, delivery: Delivery) -> Branch:
  match cleanup:
    case Clears{}: Executed{r, ctx, frames, prepared, delivery}
    case ErrorCleanup{id, fatal}:
      FailureBefore{AfterPrepare{r, ctx, frames, prepared}, X.Prepare{}, id, fatal, delivery}
    case FatalAfterStore{stage, id}: FatalAfterPublication{r, ctx, frames, prepared, stage, id}
    case PendingCleanup{}: Pending{AfterPrepare{r, ctx, frames, prepared}}

def decide_execution(r: P.Request, ctx: D.Context, output: OutputExecution,
  cleanup: Cleanup, delivery: Delivery) -> Branch:
  match output:
    case Finalized{frames, prepared}: decide_cleanup(r, ctx, frames, prepared, cleanup, delivery)
    case ErrorExecution{point, stage, id, fatal}:
      FailureBefore{phase_of_error(point, r, ctx), stage, id, fatal, delivery}
    case PendingExecution{point}: Pending{phase_of_error(point, r, ctx)}

def decide_judgment(r: P.Request, ctx: D.Context, data: DataTools) -> Branch:
  DataTools{judgment, execution, cleanup, delivery, pre} = data
  match judgment:
    case Accepted{}: decide_execution(r, ctx, execution, cleanup, delivery)
    case Refused{}: GateRefusal{r, ctx, delivery}
    case ErrorJudgment{id, fatal}: FailureBefore{AfterAuthenticate{r, ctx}, X.Verify{}, id, fatal, delivery}
    case PendingJudgment{}: Pending{AfterAuthenticate{r, ctx}}

def decide_identity(ctx: Maybe<&2, D.Context>, r: P.Request, data: DataTools) -> Branch:
  match ctx:
    case None{}:
      DataTools{judgment, execution, cleanup, delivery, pre} = data
      AutRefusal{r, delivery}
    case Some{c}: decide_judgment(r, c, data)

def decide_authentication(pre: Preprocessing, state: D.State, +r: P.Request, data: DataTools) -> Branch:
  match pre:
    case FailureAuth{id, fatal}: FailureBefore{AfterReceive{r}, X.Authenticate{}, id, fatal, delivery_of(data)}
    case PendingAuth{}: Pending{AfterReceive{r}}
    case _: decide_identity(D.authenticate(state, I.credential(r)), r, data)

def decide_pre(input: E.PreAuthentication, +data: DataTools) -> Branch:
  match input:
    case E.InputReady{state, +r}:
      decide_authentication(preprocessing(data), state, r, data)
    case E.ErrorMessage{status}:
      DataTools{judgment, execution, cleanup, delivery, pre} = data
      InputRefusal{error_of_message(status), False{}, delivery}
    case E.ErrorTransport{}:
      DataTools{judgment, execution, cleanup, delivery, pre} = data
      FailureBefore{BeforeInput{}, X.Frame{}, "internal_transport", False{}, delivery}

def decide_decode(pre: Preprocessing, bytes: List<&2, U32>, e: D.Schema,
  lim: S.Limits, data: DataTools) -> Branch:
  match pre:
    case FailureDecode{id, fatal}: FailureBefore{BeforeInput{}, X.Frame{}, id, fatal, delivery_of(data)}
    case PendingDecode{}: Pending{BeforeInput{}}
    case _: decide_pre(E.decode(bytes, e, lim), data)

# The private packet is constructed, not received as an arbitrary result.
def decide_packet(packet: Maybe<&2, List<&2, U32>>, e: D.Schema,
  lim: S.Limits, +data: DataTools) -> Branch:
  match packet:
    case None{}:
      DataTools{judgment, execution, cleanup, delivery, pre} = data
      FailureBefore{BeforeInput{}, X.Frame{}, "internal_transport", False{}, delivery}
    case Some{bytes}: decide_decode(preprocessing(data), bytes, e, lim, data)

# External reception decides closure before analyzing the private packet.
def decide_disposition(d: X.Disposition, state: List<&2, U32>, e: D.Schema,
  lim: S.Limits, data: DataTools) -> Branch:
  match d:
    case X.CloseWithoutResponse{}: WithoutResponse{}
    case X.RefuseClose{s}:
      DataTools{judgment, execution, cleanup, delivery, pre} = data
      InputRefusal{error_of_message(s), True{}, delivery}
    case X.RefuseContinue{s}:
      DataTools{judgment, execution, cleanup, delivery, pre} = data
      InputRefusal{error_of_message(s), False{}, delivery}
    case X.ProcessBody{body}: decide_packet(T.join(state, body), e, lim, data)

def decide_framing(pre: Preprocessing, d: X.Disposition, state: List<&2, U32>,
  e: D.Schema, lim: S.Limits, data: DataTools) -> Branch:
  match pre:
    case FailureFraming{id, fatal}: FailureBefore{BeforeInput{}, X.Frame{}, id, fatal, delivery_of(data)}
    case PendingFraming{}: Pending{BeforeInput{}}
    case _: decide_disposition(d, state, e, lim, data)

def decide(c: S.Configuration, reception: X.Reception, state: List<&2, U32>, +data: DataTools) -> Branch:
  match c:
    case S.Configuration{+e, laws, +lim, amb}:
      decide_framing(preprocessing(data), X.decide_reception_in(lim, reception), state, e, lim, data)


# Actual initial-worker and host-action result before Database.
# The marker is true only after the valid CheckedConfiguration branch.
type ResultInitial is Data:
  InitializationFinished{}
  FailedInitial{proof_accepts: Bool, stage: X.Stage, identifier: String, fatal: Bool}
  PendingInitial{proof_accepts: Bool}

def decide_accepted_initial(result: ResultInitial, is_valid: Bool) -> Branch:
  match result:
    case InitializationFinished{}:
      match is_valid:
        case False{}: InitialRefusal{S.DataError{}}
        case True{}: InitialOk{}
    case FailedInitial{accepts, stage, id, fatal}: InitialFailure{accepts && is_valid, stage, id, fatal}
    case PendingInitial{accepts}: InitialPending{accepts && is_valid}

# The checker precedes the worker. A worker that has not returned does not prove
# native configuration validation executed, even if it would be True.
def decide_judgment_initial(judgment: Judgment, result: ResultInitial, is_valid: Bool) -> Branch:
  match judgment:
    case Accepted{}: decide_accepted_initial(result, is_valid)
    case Refused{}: InitialRefusal{S.Certificate{}}
    case ErrorJudgment{id, fatal}: InitialFailure{False{}, X.Verify{}, id, fatal}
    case PendingJudgment{}: InitialPending{False{}}

def decide_initial_cases(is_valid: Bool, judgment: Judgment) -> Branch:
  decide_judgment_initial(judgment, InitializationFinished{}, is_valid)

def decide_result_initial(c: S.Configuration, identity: String,
  judgment: Judgment, result: ResultInitial) -> Branch:
  decide_judgment_initial(judgment, result, C.is_valid(c, identity))

def decide_initial(c: S.Configuration, identity: String, judgment: Judgment) -> Branch:
  decide_result_initial(c, identity, judgment, InitializationFinished{})

# The observed list is this generation's result, not client-supplied input.
def generate(c: S.Configuration, reception: X.Reception, state: List<&2, U32>,
  initial: D.State, data: DataTools, micro: Micro) -> List<&2, Q.Frame>:
  render(micro, initial, decide(c, reception, state, data))

def generate_result_initial(c: S.Configuration, identity: String, initial: D.State,
  judgment: Judgment, result: ResultInitial, micro: Micro) -> List<&2, Q.Frame>:
  render(micro, initial, decide_result_initial(c, identity, judgment, result))

# Success specialization used by concluded-path lemmas.
def generate_initial(c: S.Configuration, identity: String, initial: D.State,
  judgment: Judgment, micro: Micro) -> List<&2, Q.Frame>:
  generate_result_initial(c, identity, initial, judgment, InitializationFinished{}, micro)

# The service decision is never initialization.
def starts(branch: Branch) -> Bool:
  match branch:
    case InitialOk{}: True{}
    case InitialFailure{accepts, stage, id, fatal}: accepts
    case InitialPending{accepts}: accepts
    case _: False{}

def cleanup_negative_starts(r: P.Request, ctx: D.Context, qs: List<&2, Q.FrameExec>,
  p: N.Prepared, l: Cleanup, delivery: Delivery) ->
  {starts(decide_cleanup(r, ctx, qs, p, l, delivery)) == False{} : Bool}:
  match l:
    case Clears{}: {==}
    case ErrorCleanup{id, fatal}: {==}
    case FatalAfterStore{stage, id}: {==}
    case PendingCleanup{}: {==}

def execution_negative_starts(r: P.Request, ctx: D.Context, output: OutputExecution,
  l: Cleanup, delivery: Delivery) ->
  {starts(decide_execution(r, ctx, output, l, delivery)) == False{} : Bool}:
  match output:
    case Finalized{qs, p}: cleanup_negative_starts(r, ctx, qs, p, l, delivery)
    case ErrorExecution{point, stage, id, fatal}: {==}
    case PendingExecution{point}: {==}

def judgment_negative_starts(r: P.Request, ctx: D.Context, d: DataTools) ->
  {starts(decide_judgment(r, ctx, d)) == False{} : Bool}:
  match d:
    case DataTools{j, ex, li, en, pre}:
      match j:
        case Accepted{}: execution_negative_starts(r, ctx, ex, li, en)
        case Refused{}: {==}
        case ErrorJudgment{id, fatal}: {==}
        case PendingJudgment{}: {==}

def identity_negative_starts(ctx: Maybe<&2, D.Context>, r: P.Request, d: DataTools) ->
  {starts(decide_identity(ctx, r, d)) == False{} : Bool}:
  match ctx:
    case None{}:
      DataTools{ju, ex, li, en, pre} = d
      {==}
    case Some{c}: judgment_negative_starts(r, c, d)

def authentication_negative_starts(pre: Preprocessing, state: D.State, +r: P.Request, d: DataTools) ->
  {starts(decide_authentication(pre, state, r, d)) == False{} : Bool}:
  match pre:
    case FailureAuth{id, fatal}: {==}
    case Normal{}: identity_negative_starts(D.authenticate(state, I.credential(r)), r, d)
    case FailureFraming{id, fatal}: identity_negative_starts(D.authenticate(state, I.credential(r)), r, d)
    case FailureDecode{id, fatal}: identity_negative_starts(D.authenticate(state, I.credential(r)), r, d)

    case PendingFraming{}: identity_negative_starts(D.authenticate(state, I.credential(r)), r, d)
    case PendingDecode{}: identity_negative_starts(D.authenticate(state, I.credential(r)), r, d)
    case PendingAuth{}: {==}

def pre_negative_starts(p: E.PreAuthentication, +d: DataTools) ->
  {starts(decide_pre(p, d)) == False{} : Bool}:
  match p:
    case E.InputReady{s, +r}: authentication_negative_starts(preprocessing(d), s, r, d)
    case E.ErrorMessage{status}:
      DataTools{ju, ex, li, en, pre} = d
      {==}
    case E.ErrorTransport{}:
      DataTools{ju, ex, li, en, pre} = d
      {==}

def decode_negative_starts(pre: Preprocessing, bs: List<&2, U32>, e: D.Schema,
  l: S.Limits, d: DataTools) ->
  {starts(decide_decode(pre, bs, e, l, d)) == False{} : Bool}:
  match pre:
    case FailureDecode{id, fatal}: {==}
    case Normal{}: pre_negative_starts(E.decode(bs, e, l), d)
    case FailureFraming{id, fatal}: pre_negative_starts(E.decode(bs, e, l), d)
    case FailureAuth{id, fatal}: pre_negative_starts(E.decode(bs, e, l), d)

    case PendingFraming{}: pre_negative_starts(E.decode(bs, e, l), d)
    case PendingDecode{}: {==}
    case PendingAuth{}: pre_negative_starts(E.decode(bs, e, l), d)

def packet_negative_starts(p: Maybe<&2, List<&2, U32>>, e: D.Schema,
  l: S.Limits, +d: DataTools) ->
  {starts(decide_packet(p, e, l, d)) == False{} : Bool}:
  match p:
    case None{}:
      DataTools{ju, ex, li, en, pre} = d
      {==}
    case Some{bs}: decode_negative_starts(preprocessing(d), bs, e, l, d)

def disposition_negative_starts(x: X.Disposition, s: List<&2, U32>, e: D.Schema,
  l: S.Limits, d: DataTools) ->
  {starts(decide_disposition(x, s, e, l, d)) == False{} : Bool}:
  match x:
    case X.CloseWithoutResponse{}: {==}
    case X.RefuseClose{status}:
      DataTools{ju, ex, li, en, pre} = d
      {==}
    case X.RefuseContinue{status}:
      DataTools{ju, ex, li, en, pre} = d
      {==}
    case X.ProcessBody{bs}: packet_negative_starts(T.join(s, bs), e, l, d)

def framing_negative_starts(pre: Preprocessing, x: X.Disposition, s: List<&2, U32>,
  e: D.Schema, l: S.Limits, d: DataTools) ->
  {starts(decide_framing(pre, x, s, e, l, d)) == False{} : Bool}:
  match pre:
    case FailureFraming{id, fatal}: {==}
    case Normal{}: disposition_negative_starts(x, s, e, l, d)
    case FailureDecode{id, fatal}: disposition_negative_starts(x, s, e, l, d)
    case FailureAuth{id, fatal}: disposition_negative_starts(x, s, e, l, d)

    case PendingFraming{}: {==}
    case PendingDecode{}: disposition_negative_starts(x, s, e, l, d)
    case PendingAuth{}: disposition_negative_starts(x, s, e, l, d)

law service_negative_starts:
  for c: S.Configuration
  for r: X.Reception
  for s: List<&2, U32>
  for +d: DataTools
  {starts(decide(c, r, s, d)) == False{} : Bool}
def service_negative_starts(c, r, s, d):
  match c:
    case S.Configuration{+e, laws, +l, amb}:
      framing_negative_starts(preprocessing(d), X.decide_reception_in(l, r), s, e, l, d)
