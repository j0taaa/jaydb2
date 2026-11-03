# Progress from actual primitive returns, without deadline or quota.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Interface.bend as I
import ../contract/LAWS.bend as K
import ../contract/Logic.bend as L
import ../contract/Protocol.bend as P
import ../contract/Resources.bend as X
import ../contract/Requirements.bend as R
import ../contract/Semantics.bend as S
import ../src/Input.bend as Input
import ../src/Codec.bend as Codec
import ../src/ConfigurationCheck.bend as Config
import ../src/Core.bend as N
import ../src/Transport.bend as Transport
import ./SourceService.bend as Source
import ./RoutesService.bend as H
import ./ProtocolService.bend as Q
import ./Foundations.bend as F
import ./Call.bend as Call
import ./Preparation.bend as Preparation
import ./ConclusionService.bend as Conclusion
import ./Law2Service.bend as Two
import ./Law5Service.bend as Five
import ./Input.bend as InputComplete
import ./InputService.bend as Copy
import ./ModelService.bend as Model
import ./ScenariosService.bend as Scenarios
import ./HistoryService.bend as History
import ./Configuration.bend as Configuration

# Query witnesses, produced by constructors below.
def ExistsFrame(-qs: List<&2, Q.Frame>, -q: Q.Frame) -> Type:
  &t: Nat -> {Q.query(qs, t) == Some{q} : Maybe<&2, Q.Frame>}

def End(-disposition: X.Disposition, -qs: List<&2, Q.Frame>) -> Type:
  L.Disjunction<L.E<{disposition == X.CloseWithoutResponse{} : X.Disposition}, ExistsFrame(qs, Q.Closed{})>,
    &r: S.Response -> &s: D.State -> &closes: Bool -> &bs: List<&2, U32> ->
      L.E<ExistsFrame(qs, Q.Completed{r, s, closes}), ExistsFrame(qs, Q.Delivered{bs})>>

def shift_existence(+prefix: List<&2, Q.Frame>, +qs: List<&2, Q.Frame>, +q: Q.Frame,
  exists: ExistsFrame(qs, q)) -> ExistsFrame(Q.concatenate(prefix, qs), q):
  match exists:
    case (+t, query_result):
      (Nat.add(Q.size(prefix), t), Equal.trans(Maybe<&2, Q.Frame>,
        Q.query(Q.concatenate(prefix, qs), Nat.add(Q.size(prefix), t)), Q.query(qs, t), Some{q},
        Q.query_after_prefix(prefix, qs, t), query_result))

def shift_end(+prefix: List<&2, Q.Frame>, +qs: List<&2, Q.Frame>, -d: X.Disposition,
  end: End(d, qs)) -> End(d, Q.concatenate(prefix, qs)):
  match end:
    case L.Left{L.Both{disposition, closes}}: L.Left{L.Both{disposition, shift_existence(prefix, qs, Q.Closed{}, closes)}}
    case L.Right{(+r, +s, +closes, +bs, L.Both{concluded, delivered})}:
      L.Right{(r, s, closes, bs, L.Both{
        shift_existence(prefix, qs, Q.Completed{r, s, closes}, concluded), shift_existence(prefix, qs, Q.Delivered{bs}, delivered)})}

def end_of_conclusion(+s: D.State, +r: S.Response, +bs: List<&2, U32>, +closes: Bool, +next: Bool, -d: X.Disposition) ->
  End(d, H.render_conclusion(N.Conclusion{s, r, bs}, closes, H.Complete{next})):
  F.combined_pair(End(d, H.render_conclusion(N.Conclusion{s, r, bs}, closes, H.Complete{next})),
    {Q.query(H.render_conclusion(N.Conclusion{s, r, bs}, closes, H.Complete{next}), Conclusion.local_conclusion(s, r, bs)) == Some{Q.Completed{r, s, closes}} : Maybe<&2, Q.Frame>},
    {Q.query(H.render_conclusion(N.Conclusion{s, r, bs}, closes, H.Complete{next}), Succ{Conclusion.local_conclusion(s, r, bs)}) == Some{Q.Delivered{bs}} : Maybe<&2, Q.Frame>},
    Q.two_frames_after_prefix(Con{Q.Prepared{r, bs}, H.render_publication(r, s)}, H.later_delivery(closes, s, next), Q.Completed{r, s, closes}, Q.Delivered{bs}),
    concluded => delivered => L.Right{(r, s, closes, bs, L.Both{(Conclusion.local_conclusion(s, r, bs), concluded), (Succ{Conclusion.local_conclusion(s, r, bs)}, delivered)})})

def end_prepared(p: N.Prepared, +s: D.State, +next: Bool, -d: X.Disposition) ->
  End(d, H.render_final(p, s, False{}, H.Complete{next})):
  match p:
    case N.Prepared{w, ts, +r, +bs}: end_of_conclusion(S.publish(r, s, w), r, bs, False{}, next, d)

def end_error_framed(+r: S.Response, +s: D.State, +closes: Bool, +next: Bool, -d: X.Disposition,
  +bs: List<&2, U32>, framed: {P.frame(S.response_value(r)) == Some{bs} : Maybe<&2, List<&2, U32>>}) ->
  End(d, H.render_error_framed(P.frame(S.response_value(r)), r, s, closes, H.Complete{next})):
  %Equal.sym(Maybe<&2, List<&2, U32>>, P.frame(S.response_value(r)), Some{bs}, framed) :
    End(d, H.render_error_framed(_, r, s, closes, H.Complete{next}))
  L.Right{(r, s, closes, bs, L.Both{(1n, {==}), (2n, {==})})}

def end_error_message(~c: S.Configuration, +status: S.Status, +s: D.State, +closes: Bool, +next: Bool, -d: X.Disposition,
  message: &bs: List<&2, U32> -> P.Message(S.response_value(S.response_error(status)), bs)) ->
  End(d, H.render_error(status, s, closes, H.Complete{next})):
  match message:
    case (+bs, framed): end_error_framed(S.response_error(status), s, closes, next, d, bs, framed)

def end_error(~c: S.Configuration, +status: S.Status, +s: D.State, +closes: Bool, +next: Bool, -d: X.Disposition,
  +limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool}, error: Preparation.Error(status)) ->
  End(d, H.render_error(status, s, closes, H.Complete{next})):
  F.combined_pair(End(d, H.render_error(status, s, closes, H.Complete{next})),
    I.ErrorFixed(S.response_error(status)), {R.fits(R.limit_response(S.limits(c)), S.response_value(S.response_error(status))) == True{} : Bool},
    Preparation.error_preparable(status, S.limits(c), limits, error),
    payload => fits => end_error_message(c, status, s, closes, next, d,
      Call.response_preparable_has_framing(S.response_value(S.response_error(status)), S.limits(c),
        limits, fits)))

def end_combined_configuration(+qs: List<&2, Q.Frame>, -d: X.Disposition, end: End(d, qs)) -> End(d, Con{Q.Configured{}, qs}):
  shift_end([Q.Configured{}], qs, d, end)

def end_render_executed(+m: H.Micro, +s: D.State, +r: P.Request, +ctx: D.Context,
  +xs: List<&2, Q.FrameExec>, +p: N.Prepared, +next: Bool, -d: X.Disposition) ->
  End(d, H.render(m, s, H.Executed{r, ctx, xs, p, H.Complete{next}})):
  end_combined_configuration(Q.concatenate(H.render_execution(m, r, ctx, xs), Q.concatenate(H.micro_output(m), H.render_final(p, s, False{}, H.Complete{next}))), d,
    shift_end(H.render_execution(m, r, ctx, xs), Q.concatenate(H.micro_output(m), H.render_final(p, s, False{}, H.Complete{next})), d,
      shift_end(H.micro_output(m), H.render_final(p, s, False{}, H.Complete{next}), d, end_prepared(p, s, next, d))))

def error_of_input_and_fixed(error: H.ErrorInput) -> Preparation.Error(H.status_input(error)):
  match error:
    case H.Input{}: Unit{}
    case H.Limit{}: Unit{}

def end_render_input(~c: S.Configuration, +m: H.Micro, +s: D.State, +error: H.ErrorInput,
  +closes: Bool, +next: Bool, -d: X.Disposition, +limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool}) ->
  End(d, H.render(m, s, H.InputRefusal{error, closes, H.Complete{next}})):
  end_combined_configuration(Q.concatenate(H.micro_input(m), H.render_error(H.status_input(error), s, closes, H.Complete{next})), d,
    shift_end(H.micro_input(m), H.render_error(H.status_input(error), s, closes, H.Complete{next}), d,
      end_error(c, H.status_input(error), s, closes, next, d, limits, error_of_input_and_fixed(error))))

def end_render_aut(~c: S.Configuration, +m: H.Micro, +s: D.State, +r: P.Request,
  +next: Bool, -d: X.Disposition, limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool}) ->
  End(d, H.render(m, s, H.AutRefusal{r, H.Complete{next}})):
  end_combined_configuration(Q.concatenate(H.render_received(m, r), Q.concatenate(H.micro_authentication(m), Con{Q.Authenticated{r, None{}}, H.render_error(S.Authentication{}, s, False{}, H.Complete{next})})), d,
    shift_end(H.render_received(m, r), Q.concatenate(H.micro_authentication(m), Con{Q.Authenticated{r, None{}}, H.render_error(S.Authentication{}, s, False{}, H.Complete{next})}), d,
      shift_end(H.micro_authentication(m), Con{Q.Authenticated{r, None{}}, H.render_error(S.Authentication{}, s, False{}, H.Complete{next})}, d,
        shift_end([Q.Authenticated{r, None{}}], H.render_error(S.Authentication{}, s, False{}, H.Complete{next}), d,
          end_error(c, S.Authentication{}, s, False{}, next, d, limits, Unit{})))))

def end_render_gate(~c: S.Configuration, +m: H.Micro, +s: D.State, +r: P.Request, +ctx: D.Context,
  +next: Bool, -d: X.Disposition, limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool}) ->
  End(d, H.render(m, s, H.GateRefusal{r, ctx, H.Complete{next}})):
  end_combined_configuration(Q.concatenate(H.render_authenticated(m, r, ctx), Con{Q.Rejected{r, ctx}, H.render_error(S.Certificate{}, s, False{}, H.Complete{next})}), d,
    shift_end(H.render_authenticated(m, r, ctx), Con{Q.Rejected{r, ctx}, H.render_error(S.Certificate{}, s, False{}, H.Complete{next})}, d,
      shift_end([Q.Rejected{r, ctx}], H.render_error(S.Certificate{}, s, False{}, H.Complete{next}), d,
        end_error(c, S.Certificate{}, s, False{}, next, d, limits, Unit{}))))

def end_render_failure(~c: S.Configuration, +m: H.Micro, +s: D.State, +next: Bool, -d: X.Disposition,
  limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool}) ->
  End(d, H.render(m, s, H.FailureBefore{H.BeforeInput{}, X.Frame{}, "internal_transport", False{}, H.Complete{next}})):
  end_combined_configuration(Q.concatenate(H.micro_input(m), H.render_failure(s, X.Frame{}, "internal_transport", False{}, H.Complete{next})), d,
    shift_end(H.micro_input(m), H.render_failure(s, X.Frame{}, "internal_transport", False{}, H.Complete{next}), d,
      shift_end([Q.Failed{X.Frame{}, "internal_transport", False{}}], H.render_error(S.Failure{}, s, False{}, H.Complete{next}), d,
        end_error(c, S.Failure{}, s, False{}, next, d, limits, Unit{}))))

# Completeness of tool/worker calls, not protocol events.
def JudgmentTerminated(j: H.Judgment) -> Type:
  match j:
    case H.Accepted{}: Unit
    case H.Refused{}: Unit
    case H.ErrorJudgment{id, fatal}: Empty
    case H.PendingJudgment{}: Empty

def WroteEverything(delivery: H.Delivery) -> Type:
  &next: Bool -> {delivery == H.Complete{next} : H.Delivery}

def NativeReturn(-output: H.OutputExecution, -cleanup: H.Cleanup) -> Type:
  &xs: List<&2, Q.FrameExec> -> &p: N.Prepared ->
    L.E<{output == H.Finalized{xs, p} : H.OutputExecution}, {cleanup == H.Clears{} : H.Cleanup}>

def NativeReturnValue(~source: Source.Source, -c: S.Configuration, +origin: Source.JudgmentSyntactic,
  -s: D.State, -r: P.Request, -ctx: D.Context, -output: H.OutputExecution, -cleanup: H.Cleanup) -> Type:
  I.Terminates(Source.program(source, origin), S.schema(c), s, ctx, I.arguments(r)) -> NativeReturn(output, cleanup)

def output(data: H.DataTools) -> H.OutputExecution:
  match data:
    case H.DataTools{j, ex, li, en, pre}: ex

def cleanup(data: H.DataTools) -> H.Cleanup:
  match data:
    case H.DataTools{j, ex, li, en, pre}: li

def ReturnsInPre(~source: Source.Source, ~c: S.Configuration, +origin: Source.JudgmentSyntactic,
  +data: H.DataTools, pre: Input.PreAuthentication) -> Type:
  match pre:
    case Input.InputReady{s, r}:
      @ctx: D.Context -> {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>} ->
        L.E<Source.JudgmentClientReal(source, c, r, ctx, origin, H.judgment_of(data)),
          NativeReturnValue(source, c, origin, s, r, ctx, output(data), cleanup(data))>
    case _: Unit

def ReturnsInPacket(~source: Source.Source, ~c: S.Configuration, +origin: Source.JudgmentSyntactic,
  +data: H.DataTools, packet: Maybe<&2, List<&2, U32>>) -> Type:
  match packet:
    case None{}: Unit
    case Some{bs}: ReturnsInPre(source, c, origin, data, Input.decode(bs, S.schema(c), S.limits(c)))

def ReturnsInDisposition(~source: Source.Source, ~c: S.Configuration, +origin: Source.JudgmentSyntactic,
  +be: List<&2, U32>, +data: H.DataTools, disposition: X.Disposition) -> Type:
  match disposition:
    case X.ProcessBody{br}: ReturnsInPacket(source, c, origin, data, Transport.join(be, br))
    case _: Unit

def end_of_return(+m: H.Micro, +s: D.State, +r: P.Request, +ctx: D.Context,
  +output: H.OutputExecution, +cleanup: H.Cleanup, +next: Bool, -d: X.Disposition, returned: NativeReturn(output, cleanup)) ->
  End(d, H.render(m, s, H.decide_execution(r, ctx, output, cleanup, H.Complete{next}))):
  match returned:
    case (+xs, +p, L.Both{execution, clears}):
      %Equal.sym(H.OutputExecution, output, H.Finalized{xs, p}, execution) :
        End(d, H.render(m, s, H.decide_execution(r, ctx, _, cleanup, H.Complete{next})))
      %Equal.sym(H.Cleanup, cleanup, H.Clears{}, clears) :
        End(d, H.render(m, s, H.decide_execution(r, ctx, H.Finalized{xs, p}, _, H.Complete{next})))
      end_render_executed(m, s, r, ctx, xs, p, next, d)

def end_after_judgment(~source: Source.Source, ~c: S.Configuration, +origin: Source.JudgmentSyntactic,
  +m: H.Micro, +s: D.State, +decoded: D.State, +r: P.Request, +ctx: D.Context,
  j: H.Judgment, +output: H.OutputExecution, +cleanup: H.Cleanup, +next: Bool, -d: X.Disposition,
  limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool}, terminated: JudgmentTerminated(j),
  checked: Source.JudgmentClientReal(source, c, r, ctx, origin, j),
  runtime: NativeReturnValue(source, c, origin, decoded, r, ctx, output, cleanup)) ->
  End(d, H.render(m, s, H.decide_judgment(r, ctx, H.DataTools{j, output, cleanup, H.Complete{next}, H.Normal{}}))):
  match j:
    case H.Accepted{}:
      match checked:
        case L.Both{el, L.Both{de, L.Both{cert, L.Both{dt, terminates}}}}:
          end_of_return(m, s, r, ctx, output, cleanup, next, d, runtime(terminates(decoded, ctx, I.arguments(r))))
    case H.Refused{}: end_render_gate(c, m, s, r, ctx, next, d, limits)
    case H.ErrorJudgment{id, fatal}: L.ex_false(End(d, H.render(m, s, H.decide_judgment(r, ctx, H.DataTools{H.ErrorJudgment{id, fatal}, output, cleanup, H.Complete{next}, H.Normal{}}))), terminated)
    case H.PendingJudgment{}: L.ex_false(End(d, H.render(m, s, H.decide_judgment(r, ctx, H.DataTools{H.PendingJudgment{}, output, cleanup, H.Complete{next}, H.Normal{}}))), terminated)

def end_of_identity(~source: Source.Source, ~c: S.Configuration, +origin: Source.JudgmentSyntactic,
  +m: H.Micro, +s: D.State, +decoded: D.State, +r: P.Request, identity: Maybe<&2, D.Context>,
  +j: H.Judgment, +ex: H.OutputExecution, +li: H.Cleanup, +next: Bool, -d: X.Disposition,
  limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool}, terminated: JudgmentTerminated(j),
  returns: @ctx: D.Context -> {identity == Some{ctx} : Maybe<&2, D.Context>} ->
    L.E<Source.JudgmentClientReal(source, c, r, ctx, origin, j), NativeReturnValue(source, c, origin, decoded, r, ctx, ex, li)>) ->
  End(d, H.render(m, s, H.decide_identity(identity, r, H.DataTools{j, ex, li, H.Complete{next}, H.Normal{}}))):
  match identity:
    case None{}: end_render_aut(c, m, s, r, next, d, limits)
    case Some{+ctx}:
      F.combined_pair(End(d, H.render(m, s, H.decide_identity(Some{ctx}, r, H.DataTools{j, ex, li, H.Complete{next}, H.Normal{}}))),
        Source.JudgmentClientReal(source, c, r, ctx, origin, j), NativeReturnValue(source, c, origin, decoded, r, ctx, ex, li), returns(ctx, {==}),
        checked => runtime => end_after_judgment(source, c, origin, m, s, decoded, r, ctx, j, ex, li, next, d, limits, terminated, checked, runtime))

def end_of_input(~source: Source.Source, ~c: S.Configuration, +origin: Source.JudgmentSyntactic,
  +m: H.Micro, +s: D.State, pre: Input.PreAuthentication,
  +j: H.Judgment, +ex: H.OutputExecution, +li: H.Cleanup, +next: Bool, -d: X.Disposition,
  limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool}, terminated: JudgmentTerminated(j),
  returns: ReturnsInPre(source, c, origin, H.DataTools{j, ex, li, H.Complete{next}, H.Normal{}}, pre)) ->
  End(d, H.render(m, s, H.decide_pre(pre, H.DataTools{j, ex, li, H.Complete{next}, H.Normal{}}))):
  match pre:
    case Input.InputReady{+decoded, +r}:
      end_of_identity(source, c, origin, m, s, decoded, r, D.authenticate(decoded, I.credential(r)), j, ex, li, next, d, limits, terminated, returns)
    case Input.ErrorMessage{+status}: end_render_input(c, m, s, H.error_of_message(status), False{}, next, d, limits)
    case Input.ErrorTransport{}: end_render_failure(c, m, s, next, d, limits)

def end_of_packet(~source: Source.Source, ~c: S.Configuration, +origin: Source.JudgmentSyntactic,
  +m: H.Micro, +s: D.State, packet: Maybe<&2, List<&2, U32>>,
  +j: H.Judgment, +ex: H.OutputExecution, +li: H.Cleanup, +next: Bool, -d: X.Disposition,
  limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool}, terminated: JudgmentTerminated(j),
  returns: ReturnsInPacket(source, c, origin, H.DataTools{j, ex, li, H.Complete{next}, H.Normal{}}, packet)) ->
  End(d, H.render(m, s, H.decide_packet(packet, S.schema(c), S.limits(c), H.DataTools{j, ex, li, H.Complete{next}, H.Normal{}}))):
  match packet:
    case None{}: end_render_failure(c, m, s, next, d, limits)
    case Some{+bs}: end_of_input(source, c, origin, m, s, Input.decode(bs, S.schema(c), S.limits(c)), j, ex, li, next, d, limits, terminated, returns)

def end_of_disposition(~source: Source.Source, ~c: S.Configuration, +origin: Source.JudgmentSyntactic,
  +m: H.Micro, +s: D.State, +be: List<&2, U32>, +d: X.Disposition,
  +j: H.Judgment, +ex: H.OutputExecution, +li: H.Cleanup, +next: Bool,
  limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool}, terminated: JudgmentTerminated(j),
  returns: ReturnsInDisposition(source, c, origin, be, H.DataTools{j, ex, li, H.Complete{next}, H.Normal{}}, d)) ->
  End(d, H.render(m, s, H.decide_disposition(d, be, S.schema(c), S.limits(c), H.DataTools{j, ex, li, H.Complete{next}, H.Normal{}}))):
  match d:
    case X.CloseWithoutResponse{}: L.Left{L.Both{{==}, (1n, {==})}}
    case X.RefuseClose{+status}: end_render_input(c, m, s, H.error_of_message(status), True{}, next, X.RefuseClose{status}, limits)
    case X.RefuseContinue{+status}: end_render_input(c, m, s, H.error_of_message(status), False{}, next, X.RefuseContinue{status}, limits)
    case X.ProcessBody{+br}: end_of_packet(source, c, origin, m, s, Transport.join(be, br), j, ex, li, next, X.ProcessBody{br}, limits, terminated, returns)

# Availability describes read/checker/worker/cleanup/write returns.
# It does not redefines Processable or supply Concluded, Accepts or Started.
def ToolsAvailable(~source: Source.Source, ~c: S.Configuration, +origin: Source.JudgmentSyntactic,
  +be: List<&2, U32>, +input: X.Reception, data: H.DataTools) -> Type:
  L.E<{H.preprocessing(data) == H.Normal{} : H.Preprocessing},
    L.E<WroteEverything(H.delivery_of(data)),
      L.E<JudgmentTerminated(H.judgment_of(data)), ReturnsInDisposition(source, c, origin, be, data, X.decide_reception(c, input))>>>

def end_of_tools_normal(~source: Source.Source, ~c: S.Configuration, +origin: Source.JudgmentSyntactic,
  +m: H.Micro, +s: D.State, +be: List<&2, U32>, +input: X.Reception,
  +j: H.Judgment, +ex: H.OutputExecution, +li: H.Cleanup, +en: H.Delivery, +pre: H.Preprocessing, +next: Bool,
  limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool},
  normal: {pre == H.Normal{} : H.Preprocessing}, write: {en == H.Complete{next} : H.Delivery}, terminated: JudgmentTerminated(j),
  returns: ReturnsInDisposition(source, c, origin, be, H.DataTools{j, ex, li, en, pre}, X.decide_reception(c, input))) ->
  End(X.decide_reception(c, input), H.render(m, s, H.decide(c, input, be, H.DataTools{j, ex, li, en, pre}))):
  F.combined_pair(End(X.decide_reception(c, input), H.render(m, s, H.decide(c, input, be, H.DataTools{j, ex, li, en, pre}))),
    {pre == H.Normal{} : H.Preprocessing}, {pre == H.Normal{} : H.Preprocessing},
    Call.duplicate_equality(H.Preprocessing, pre, H.Normal{}, normal), n1 => n2 =>
      F.combined_pair(End(X.decide_reception(c, input), H.render(m, s, H.decide(c, input, be, H.DataTools{j, ex, li, en, pre}))),
        {en == H.Complete{next} : H.Delivery}, {en == H.Complete{next} : H.Delivery},
        Call.duplicate_equality(H.Delivery, en, H.Complete{next}, write), e1 => e2 =>
          %Equal.sym(H.Preprocessing, pre, H.Normal{}, n1) :
            End(X.decide_reception(c, input), H.render(m, s, H.decide(c, input, be, H.DataTools{j, ex, li, en, _})))
          %Equal.sym(H.Delivery, en, H.Complete{next}, e1) :
            End(X.decide_reception(c, input), H.render(m, s, H.decide(c, input, be, H.DataTools{j, ex, li, _, H.Normal{}})))
          %Equal.sym(H.Branch, H.decide(c, input, be, H.DataTools{j, ex, li, H.Complete{next}, H.Normal{}}),
            H.decide_framing(H.Normal{}, X.decide_reception(c, input), be, S.schema(c), S.limits(c), H.DataTools{j, ex, li, H.Complete{next}, H.Normal{}}),
            Two.decide_by_reception(c, input, be, H.DataTools{j, ex, li, H.Complete{next}, H.Normal{}})) :
              End(X.decide_reception(c, input), H.render(m, s, _))
          end_of_disposition(source, c, origin, m, s, be, X.decide_reception(c, input), j, ex, li, next, limits, terminated,
            (%n2 : ReturnsInDisposition(source, c, origin, be, H.DataTools{j, ex, li, H.Complete{next}, _}, X.decide_reception(c, input))
              %e2 : ReturnsInDisposition(source, c, origin, be, H.DataTools{j, ex, li, _, pre}, X.decide_reception(c, input)) returns))))

def end_of_tools(~source: Source.Source, ~c: S.Configuration, +origin: Source.JudgmentSyntactic,
  +m: H.Micro, +s: D.State, +be: List<&2, U32>, +input: X.Reception, data: H.DataTools,
  limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool}, available: ToolsAvailable(source, c, origin, be, input, data)) ->
  End(X.decide_reception(c, input), H.render(m, s, H.decide(c, input, be, data))):
  match data available:
    case H.DataTools{+j, +ex, +li, +en, +pre} L.Both{normal, L.Both{(+next, write), L.Both{terminated, returns}}}:
      end_of_tools_normal(source, c, origin, m, s, be, input, j, ex, li, en, pre, next, limits, normal, write, terminated, returns)

# A query becomes a fact only through the fixed renderer and source.
def EventOfProgress(f: I.Fact) -> Type:
  match f:
    case I.Concluded{r, s, closes}: Unit
    case I.DeliveredEverything{bs}: Unit
    case I.ClosedChannel{}: Unit
    case I.CertificateAccepted{r, ctx, p}: Unit
    case I.ProgramStarted{r, ctx, p}: Unit
    case _: Empty

def query_observable(-c: S.Configuration, -root: S.Program, +ini: Maybe<&2, D.State>, +qs: List<&2, Q.Frame>,
  +t: Nat, +q: Q.Frame, f: I.Fact, event: EventOfProgress(f),
  relation: Q.rel_fact(c, root, q, f), query_result: {Q.query(qs, t) == Some{q} : Maybe<&2, Q.Frame>}) ->
  Q.observes_service(c, root, ini, qs, t, f):
  match f:
    case I.ConfigurationInUse{other}: L.ex_false(Q.observes_service(c, root, ini, qs, t, I.ConfigurationInUse{other}), event)
    case I.ProofInitialAccepts{}: L.ex_false(Q.observes_service(c, root, ini, qs, t, I.ProofInitialAccepts{}), event)
    case I.InstanceStarted{s}: L.ex_false(Q.observes_service(c, root, ini, qs, t, I.InstanceStarted{s}), event)
    case I.InitializationRefused{s}: L.ex_false(Q.observes_service(c, root, ini, qs, t, I.InitializationRefused{s}), event)
    case I.Encoded{v, bs}: L.ex_false(Q.observes_service(c, root, ini, qs, t, I.Encoded{v, bs}), event)
    case I.Decoded{bs, v}: L.ex_false(Q.observes_service(c, root, ini, qs, t, I.Decoded{bs, v}), event)
    case I.Stored{s, bs, abstr}: L.ex_false(Q.observes_service(c, root, ini, qs, t, I.Stored{s, bs, abstr}), event)
    case I.CheckedLength{pos, n}: L.ex_false(Q.observes_service(c, root, ini, qs, t, I.CheckedLength{pos, n}), event)
    case I.AllocatedField{pos, n}: L.ex_false(Q.observes_service(c, root, ini, qs, t, I.AllocatedField{pos, n}), event)
    case I.ReadBody{before, n, declared}: L.ex_false(Q.observes_service(c, root, ini, qs, t, I.ReadBody{before, n, declared}), event)
    case I.ReceivedRequest{r}: L.ex_false(Q.observes_service(c, root, ini, qs, t, I.ReceivedRequest{r}), event)
    case I.Authenticated{r, ctx}: L.ex_false(Q.observes_service(c, root, ini, qs, t, I.Authenticated{r, ctx}), event)
    case I.CertificateAccepted{r, ctx, other}: Q.query_establishes_observation(c, root, qs, t, q, I.CertificateAccepted{r, ctx, other}, query_result, relation)
    case I.CertificateRejected{r, ctx}: L.ex_false(Q.observes_service(c, root, ini, qs, t, I.CertificateRejected{r, ctx}), event)
    case I.ProgramStarted{r, ctx, other}: Q.query_establishes_observation(c, root, qs, t, q, I.ProgramStarted{r, ctx, other}, query_result, relation)
    case I.Evaluated{r, ctx, other, execution_trace}: L.ex_false(Q.observes_service(c, root, ini, qs, t, I.Evaluated{r, ctx, other, execution_trace}), event)
    case I.Operated{e, s, o, r}: L.ex_false(Q.observes_service(c, root, ini, qs, t, I.Operated{e, s, o, r}), event)
    case I.Prepared{r, bs}: L.ex_false(Q.observes_service(c, root, ini, qs, t, I.Prepared{r, bs}), event)
    case I.Published{s}: L.ex_false(Q.observes_service(c, root, ini, qs, t, I.Published{s}), event)
    case I.StateVisible{s}: L.ex_false(Q.observes_service(c, root, ini, qs, t, I.StateVisible{s}), event)
    case I.FailedEnvironment{stage, id, fatal}: L.ex_false(Q.observes_service(c, root, ini, qs, t, I.FailedEnvironment{stage, id, fatal}), event)
    case I.Concluded{r, s, closes}: Q.query_establishes_observation(c, root, qs, t, q, I.Concluded{r, s, closes}, query_result, relation)
    case I.DeliveredEverything{bs}: Q.query_establishes_observation(c, root, qs, t, q, I.DeliveredEverything{bs}, query_result, relation)
    case I.DeliveryInterrupted{bs}: L.ex_false(Q.observes_service(c, root, ini, qs, t, I.DeliveryInterrupted{bs}), event)
    case I.ClosedChannel{}: Q.query_establishes_observation(c, root, qs, t, q, I.ClosedChannel{}, query_result, relation)
    case I.NextCall{before, after}: L.ex_false(Q.observes_service(c, root, ini, qs, t, I.NextCall{before, after}), event)
    case I.InspectionNotModeled{description}: L.ex_false(Q.observes_service(c, root, ini, qs, t, I.InspectionNotModeled{description}), event)
    case I.EffectNotModeled{description}: L.ex_false(Q.observes_service(c, root, ini, qs, t, I.EffectNotModeled{description}), event)

def RelationOfOrigin(~source: Source.Source, -c: S.Configuration, origin: Maybe<&2, Source.JudgmentSyntactic>, +q: Q.Frame, -f: I.Fact) -> Type:
  match origin:
    case None{}: Q.rel_fact(c, Source.without_program(), q, f)
    case Some{origin}: Q.rel_fact(c, Source.program(source, origin), q, f)

def query_of_origin(~source: Source.Source, -c: S.Configuration, +ini: Maybe<&2, D.State>, +qs: List<&2, Q.Frame>,
  origin: Maybe<&2, Source.JudgmentSyntactic>, +t: Nat, +q: Q.Frame, f: I.Fact, event: EventOfProgress(f),
  relation: RelationOfOrigin(source, c, origin, q, f), query_result: {Q.query(qs, t) == Some{q} : Maybe<&2, Q.Frame>}) ->
  Source.of_origin(source, c, ini, qs, origin, t, f):
  match origin:
    case None{}: query_observable(c, Source.without_program(), ini, qs, t, q, f, event, relation, query_result)
    case Some{origin}: query_observable(c, Source.program(source, origin), ini, qs, t, q, f, event, relation, query_result)

def frames(data: Source.ObservationData) -> List<&2, Q.Frame>:
  match data:
    case Source.ObservationData{ini, qs, origin}: qs

def origin_of_observation(data: Source.ObservationData) -> Maybe<&2, Source.JudgmentSyntactic>:
  match data:
    case Source.ObservationData{ini, qs, origin}: origin

def query_of_observation(~source: Source.Source, -c: S.Configuration, +data: Source.ObservationData,
  +t: Nat, +q: Q.Frame, f: I.Fact, event: EventOfProgress(f),
  relation: RelationOfOrigin(source, c, origin_of_observation(data), q, f),
  query_result: {Q.query(frames(data), t) == Some{q} : Maybe<&2, Q.Frame>}) -> Source.of_observation(source, c, data, t, f):
  match data:
    case Source.ObservationData{ini, qs, origin}: query_of_origin(source, c, ini, qs, origin, t, q, f, event, relation, query_result)

def event_of_route(~source: Source.Source, ~c: S.Configuration, +x: Source.Context, +t: Nat, +q: Q.Frame, f: I.Fact,
  canonical: {Source.scenario_context(c, x) == Source.scenario(source, Source.world(Source.scenario_context(c, x))) : I.Scenario},
  event: EventOfProgress(f), relation: RelationOfOrigin(source, c, origin_of_observation(Two.data_of_route(source, c, x)), q, f),
  query_result: {Q.query(frames(Two.data_of_route(source, c, x)), t) == Some{q} : Maybe<&2, Q.Frame>}) ->
  I.Happens(Source.environment(source), Source.artifact(source), Source.scenario_context(c, x), t, f):
  Source.introduce_fact_literal(source, Source.artifact(source), Source.scenario_context(c, x), t, f,
    L.Both{{==}, L.Both{canonical, Two.observation_became_route(source, c, x, t, f,
      query_of_observation(source, c, Two.data_of_route(source, c, x), t, q, f, event, relation, query_result))}})

def relation_uniform(~source: Source.Source, -c: S.Configuration, origin: Maybe<&2, Source.JudgmentSyntactic>, +q: Q.Frame, -f: I.Fact,
  proof: @p: S.Program -> Q.rel_fact(c, p, q, f)) -> RelationOfOrigin(source, c, origin, q, f):
  match origin:
    case None{}: proof(Source.without_program())
    case Some{origin}: proof(Source.program(source, origin))

def AvailabilityOfCall(~source: Source.Source, ~c: S.Configuration, +input: X.Reception, data: Source.CallData) -> Type:
  match data:
    case Source.CallData{cf, origin, pf, tf, be, tools, micro}: ToolsAvailable(source, c, origin, be, input, tools)

def end_of_metadata(~source: Source.Source, ~c: S.Configuration, +s: D.State, +input: X.Reception, data: Source.CallData,
  limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool}, available: AvailabilityOfCall(source, c, input, data)) ->
  End(X.decide_reception(c, input), frames(Source.construct_call(c, s, input, data))):
  match data:
    case Source.CallData{cf, +origin, pf, tf, +be, tools, +micro}: end_of_tools(source, c, origin, micro, s, be, input, tools, limits, available)

def end_of_call(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +input: X.Reception,
  data: Source.CallData, same: {data == Source.call(source, world) : Source.CallData},
  limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool},
  available: AvailabilityOfCall(source, c, input, data)) ->
  End(X.decide_reception(c, input), frames(Two.data_of_route(source, c, Source.Service{world, s, input}))):
  %same : End(X.decide_reception(c, input), frames(Source.construct_call(c, s, input, _)))
  end_of_metadata(source, c, s, input, data, limits, available)

def terminate_of_source(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +input: X.Reception,
  canonical: {I.Serve{world, c, s, input} == Source.scenario(source, world) : I.Scenario},
  end: End(X.decide_reception(c, input), frames(Two.data_of_route(source, c, Source.Service{world, s, input})))) ->
  K.ServiceTerminates(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, input}):
  match end:
    case L.Left{L.Both{without_response, (+t, closed)}}:
      L.Left{L.Both{without_response, (t, event_of_route(source, c, Source.Service{world, s, input}, t, Q.Closed{}, I.ClosedChannel{},
        canonical, Unit{}, relation_uniform(source, c, origin_of_observation(Two.data_of_route(source, c, Source.Service{world, s, input})), Q.Closed{}, I.ClosedChannel{}, p => {==}), closed))}}
    case L.Right{(+r, +w, +closes, +bs, L.Both{(+tc, concluded), (+te, delivered)})}:
      F.combined_pair(K.ServiceTerminates(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, input}),
        {I.Serve{world, c, s, input} == Source.scenario(source, world) : I.Scenario},
        {I.Serve{world, c, s, input} == Source.scenario(source, world) : I.Scenario},
        Call.duplicate_equality(I.Scenario, I.Serve{world, c, s, input}, Source.scenario(source, world), canonical), c1 => c2 =>
          L.Right{(r, w, closes, L.Both{
            (tc, event_of_route(source, c, Source.Service{world, s, input}, tc, Q.Completed{r, w, closes}, I.Concluded{r, w, closes}, c1, Unit{},
              relation_uniform(source, c, origin_of_observation(Two.data_of_route(source, c, Source.Service{world, s, input})), Q.Completed{r, w, closes}, I.Concluded{r, w, closes}, p => {==}), concluded)),
            (bs, te, event_of_route(source, c, Source.Service{world, s, input}, te, Q.Delivered{bs}, I.DeliveredEverything{bs}, c2, Unit{},
              relation_uniform(source, c, origin_of_observation(Two.data_of_route(source, c, Source.Service{world, s, input})), Q.Delivered{bs}, I.DeliveredEverything{bs}, p => {==}), delivered))})})

# Parser completeness follows from canonical bytes and actual-copy measures.
def packet_ready_offers_ready(~c: S.Configuration, +world: Nat, +s: D.State, +input: X.Reception,
  +be: List<&2, U32>, +br: List<&2, U32>, +r: P.Request,
  disposition: {X.decide_reception(c, input) == X.ProcessBody{br} : X.Disposition},
  ready: InputComplete.PacketReady(S.schema(c), s, r, S.limits(c), be, br)) ->
  &body: List<&2, U32> -> &bs: List<&2, U32> -> L.E<{X.decide_reception(c, input) == X.ProcessBody{body} : X.Disposition},
    L.E<{Transport.join(be, body) == Some{bs} : Maybe<&2, List<&2, U32>>},
      {Input.decode(bs, S.schema(c), S.limits(c)) == Input.InputReady{s, r} : Input.PreAuthentication}>>:
  match ready:
    case (bs, L.Both{assembly, L.Both{ready, analysis}}): (br, bs, L.Both{disposition, L.Both{assembly, ready}})

def packet_of_request_measure(~c: S.Configuration, +world: Nat, +s: D.State, +input: X.Reception,
  +be: List<&2, U32>, +r: P.Request, +br: List<&2, U32>, +ce: B.Number64, +te: B.Number64,
  disposition: {X.decide_reception(c, input) == X.ProcessBody{br} : X.Disposition},
  cod_and: P.Encoding(D.state_value(s), be), cod_r: P.Encoding(P.request_value(r), br),
  +measure_and: {B.nat64(B.length(be)) == Some{ce} : Maybe<&2, B.Number64>},
  ceiling_and: {B.nat64(R.limit_state(S.limits(c))) == Some{te} : Maybe<&2, B.Number64>},
  fits_and: {Codec.less_equal64(ce, te) == True{} : Bool}, structure: {D.structure(S.schema(c), s) == True{} : Bool},
  measures: &cr: B.Number64 -> &tr: B.Number64 -> L.E<{B.nat64(B.length(br)) == Some{cr} : Maybe<&2, B.Number64>},
    L.E<{B.nat64(R.limit_message(S.limits(c))) == Some{tr} : Maybe<&2, B.Number64>}, {Codec.less_equal64(cr, tr) == True{} : Bool}>>) ->
  &body: List<&2, U32> -> &bs: List<&2, U32> -> L.E<{X.decide_reception(c, input) == X.ProcessBody{body} : X.Disposition},
    L.E<{Transport.join(be, body) == Some{bs} : Maybe<&2, List<&2, U32>>},
      {Input.decode(bs, S.schema(c), S.limits(c)) == Input.InputReady{s, r} : Input.PreAuthentication}>>:
  match measures:
    case (+cr, +tr, L.Both{measure_r, L.Both{ceiling_r, fits_r}}):
      packet_ready_offers_ready(c, world, s, input, be, br, r, disposition,
        InputComplete.all_input_canonical_admissible_has_packet_ready_and_analysis_exact(S.schema(c), s, r, S.limits(c), be, br, ce, cr, te, tr,
          cod_and, cod_r, measure_and, measure_r, ceiling_and, ceiling_r, fits_and, fits_r, structure))

def packet_of_request_received(~c: S.Configuration, +world: Nat, +s: D.State, +input: X.Reception,
  +be: List<&2, U32>, +r: P.Request, state: Copy.StateCopied(c, s, be), body: Copy.BodyCopied(c, input),
  structure: {D.structure(S.schema(c), s) == True{} : Bool}, received: I.RequestReceived(I.Serve{world, c, s, input}, r)) ->
  &br: List<&2, U32> -> &bs: List<&2, U32> ->
    L.E<{X.decide_reception(c, input) == X.ProcessBody{br} : X.Disposition},
      L.E<{Transport.join(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>},
        {Input.decode(bs, S.schema(c), S.limits(c)) == Input.InputReady{s, r} : Input.PreAuthentication}>>:
  match state:
    case (+ce, +te, L.Both{cod_and, L.Both{+measure_and, L.Both{ceiling_and, fits_and}}}):
      match body:
        case L.Both{is_valid, measures}:
          match received:
            case (+br, L.Both{+disposition, cod_r}):
              packet_of_request_measure(c, world, s, input, be, r, br, ce, te, disposition, cod_and, cod_r, measure_and, ceiling_and, fits_and, structure, measures(br, disposition))

def ElaborationFunctional(~source: Source.Source, ~c: S.Configuration) -> Type:
  @code: String -> @p: S.Program -> @q: S.Program ->
    L.E<Source.elaboration(source, c, code, p), Source.elaboration(source, c, code, q)> -> {p == q : S.Program}

def gate_admits_certificate(~source: Source.Source, ~c: S.Configuration, +origin: Source.JudgmentSyntactic,
  +s: D.State, +r: P.Request, +ctx: D.Context, p: S.Program,
  +j: H.Judgment, +ex: H.OutputExecution, +li: H.Cleanup,
  terminated: JudgmentTerminated(j), semantics: Source.JudgmentClientReal(source, c, r, ctx, origin, j),
  runtime: NativeReturnValue(source, c, origin, s, r, ctx, ex, li), functional: ElaborationFunctional(source, c),
  certificate: L.E<I.Bound(Source.environment(source), c, I.code(r), p),
    I.Derives(Source.environment(source), c, I.proof(r), R.Certifies(c, I.code(r), p, ctx, I.arguments(r)))>) ->
  L.E<{j == H.Accepted{} : H.Judgment}, L.E<{p == Source.program(source, origin) : S.Program}, NativeReturn(ex, li)>>:
  match j:
    case H.Accepted{}:
      match semantics certificate:
        case L.Both{elaborated, L.Both{de, L.Both{cert, L.Both{dt, terminates}}}} L.Both{L.Both{elaborated_p, terminates_p}, proof_p}:
          L.Both{{==}, L.Both{functional(I.code(r), p, Source.program(source, origin), L.Both{elaborated_p, elaborated}), runtime(terminates(s, ctx, I.arguments(r)))}}
    case H.Refused{}:
      L.ex_false(L.E<{H.Refused{} == H.Accepted{} : H.Judgment}, L.E<{p == Source.program(source, origin) : S.Program}, NativeReturn(ex, li)>>, semantics(p, certificate))
    case H.ErrorJudgment{id, fatal}:
      L.ex_false(L.E<{H.ErrorJudgment{id, fatal} == H.Accepted{} : H.Judgment}, L.E<{p == Source.program(source, origin) : S.Program}, NativeReturn(ex, li)>>, terminated)
    case H.PendingJudgment{}:
      L.ex_false(L.E<{H.PendingJudgment{} == H.Accepted{} : H.Judgment}, L.E<{p == Source.program(source, origin) : S.Program}, NativeReturn(ex, li)>>, terminated)

def extend_existence(+qs: List<&2, Q.Frame>, +suffix: List<&2, Q.Frame>, +q: Q.Frame,
  exists: ExistsFrame(qs, q)) -> ExistsFrame(Q.concatenate(qs, suffix), q):
  match exists:
    case (+t, query_result):
      (t, Q.query_prefix(qs, suffix, t, q, query_result))

def milestones_of_execution(+m: H.Micro, +s: D.State, +r: P.Request, +ctx: D.Context,
  +xs: List<&2, Q.FrameExec>, +p: N.Prepared, +next: Bool) ->
  L.E<ExistsFrame(H.render(m, s, H.Executed{r, ctx, xs, p, H.Complete{next}}), Q.Accepts{r, ctx}),
    ExistsFrame(H.render(m, s, H.Executed{r, ctx, xs, p, H.Complete{next}}), Q.Started{r, ctx})>:
  L.Both{
    shift_existence([Q.Configured{}], Q.concatenate(H.render_execution(m, r, ctx, xs), Q.concatenate(H.micro_output(m), H.render_final(p, s, False{}, H.Complete{next}))), Q.Accepts{r, ctx},
      extend_existence(H.render_execution(m, r, ctx, xs), Q.concatenate(H.micro_output(m), H.render_final(p, s, False{}, H.Complete{next})), Q.Accepts{r, ctx},
        extend_existence(H.render_started(m, r, ctx), Q.expand_exec(r, ctx, xs), Q.Accepts{r, ctx},
          extend_existence(H.render_verified(m, r, ctx), Q.concatenate(H.micro_execution(m), [Q.Started{r, ctx}]), Q.Accepts{r, ctx},
            shift_existence(H.render_authenticated(m, r, ctx), [Q.Accepts{r, ctx}], Q.Accepts{r, ctx}, (0n, {==})))))),
    shift_existence([Q.Configured{}], Q.concatenate(H.render_execution(m, r, ctx, xs), Q.concatenate(H.micro_output(m), H.render_final(p, s, False{}, H.Complete{next}))), Q.Started{r, ctx},
      extend_existence(H.render_execution(m, r, ctx, xs), Q.concatenate(H.micro_output(m), H.render_final(p, s, False{}, H.Complete{next})), Q.Started{r, ctx},
        extend_existence(H.render_started(m, r, ctx), Q.expand_exec(r, ctx, xs), Q.Started{r, ctx},
          shift_existence(H.render_verified(m, r, ctx), Q.concatenate(H.micro_execution(m), [Q.Started{r, ctx}]), Q.Started{r, ctx},
            shift_existence(H.micro_execution(m), [Q.Started{r, ctx}], Q.Started{r, ctx}, (0n, {==}))))))}

def tools_exact(+j: H.Judgment, +ex: H.OutputExecution, +li: H.Cleanup, +en: H.Delivery, +pre: H.Preprocessing,
  +xs: List<&2, Q.FrameExec>, +p: N.Prepared, +next: Bool,
  accepted: {j == H.Accepted{} : H.Judgment}, executed: {ex == H.Finalized{xs, p} : H.OutputExecution},
  cleared: {li == H.Clears{} : H.Cleanup}, wrote: {en == H.Complete{next} : H.Delivery}, normal: {pre == H.Normal{} : H.Preprocessing}) ->
  {H.DataTools{j, ex, li, en, pre} == H.DataTools{H.Accepted{}, H.Finalized{xs, p}, H.Clears{}, H.Complete{next}, H.Normal{}} : H.DataTools}:
  %Equal.sym(H.Judgment, j, H.Accepted{}, accepted) : {H.DataTools{_, ex, li, en, pre} == H.DataTools{H.Accepted{}, H.Finalized{xs, p}, H.Clears{}, H.Complete{next}, H.Normal{}} : H.DataTools}
  %Equal.sym(H.OutputExecution, ex, H.Finalized{xs, p}, executed) : {H.DataTools{H.Accepted{}, _, li, en, pre} == H.DataTools{H.Accepted{}, H.Finalized{xs, p}, H.Clears{}, H.Complete{next}, H.Normal{}} : H.DataTools}
  %Equal.sym(H.Cleanup, li, H.Clears{}, cleared) : {H.DataTools{H.Accepted{}, H.Finalized{xs, p}, _, en, pre} == H.DataTools{H.Accepted{}, H.Finalized{xs, p}, H.Clears{}, H.Complete{next}, H.Normal{}} : H.DataTools}
  %Equal.sym(H.Delivery, en, H.Complete{next}, wrote) : {H.DataTools{H.Accepted{}, H.Finalized{xs, p}, H.Clears{}, _, pre} == H.DataTools{H.Accepted{}, H.Finalized{xs, p}, H.Clears{}, H.Complete{next}, H.Normal{}} : H.DataTools}
  %Equal.sym(H.Preprocessing, pre, H.Normal{}, normal) : {H.DataTools{H.Accepted{}, H.Finalized{xs, p}, H.Clears{}, H.Complete{next}, _} == H.DataTools{H.Accepted{}, H.Finalized{xs, p}, H.Clears{}, H.Complete{next}, H.Normal{}} : H.DataTools}
  {==}

def branch_executed(~c: S.Configuration, +input: X.Reception, +be: List<&2, U32>, +data: H.DataTools,
  +s: D.State, +r: P.Request, +ctx: D.Context, +br: List<&2, U32>, +bs: List<&2, U32>,
  +xs: List<&2, Q.FrameExec>, +p: N.Prepared, +next: Bool,
  tools: {data == H.DataTools{H.Accepted{}, H.Finalized{xs, p}, H.Clears{}, H.Complete{next}, H.Normal{}} : H.DataTools},
  received: {X.decide_reception(c, input) == X.ProcessBody{br} : X.Disposition},
  assembly_result: {Transport.join(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>},
  decoded: {Input.decode(bs, S.schema(c), S.limits(c)) == Input.InputReady{s, r} : Input.PreAuthentication},
  authenticated: {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>}) ->
  {H.decide(c, input, be, data) == H.Executed{r, ctx, xs, p, H.Complete{next}} : H.Branch}:
  %Equal.sym(H.DataTools, data, H.DataTools{H.Accepted{}, H.Finalized{xs, p}, H.Clears{}, H.Complete{next}, H.Normal{}}, tools) :
    {H.decide(c, input, be, _) == H.Executed{r, ctx, xs, p, H.Complete{next}} : H.Branch}
  Equal.trans(H.Branch, H.decide(c, input, be, H.DataTools{H.Accepted{}, H.Finalized{xs, p}, H.Clears{}, H.Complete{next}, H.Normal{}}),
    H.decide_framing(H.Normal{}, X.decide_reception(c, input), be, S.schema(c), S.limits(c), H.DataTools{H.Accepted{}, H.Finalized{xs, p}, H.Clears{}, H.Complete{next}, H.Normal{}}),
    H.Executed{r, ctx, xs, p, H.Complete{next}}, Two.decide_by_reception(c, input, be, H.DataTools{H.Accepted{}, H.Finalized{xs, p}, H.Clears{}, H.Complete{next}, H.Normal{}}),
    (%Equal.sym(X.Disposition, X.decide_reception(c, input), X.ProcessBody{br}, received) :
      {H.decide_disposition(_, be, S.schema(c), S.limits(c), H.DataTools{H.Accepted{}, H.Finalized{xs, p}, H.Clears{}, H.Complete{next}, H.Normal{}}) == H.Executed{r, ctx, xs, p, H.Complete{next}} : H.Branch}
    %Equal.sym(Maybe<&2, List<&2, U32>>, Transport.join(be, br), Some{bs}, assembly_result) :
      {H.decide_packet(_, S.schema(c), S.limits(c), H.DataTools{H.Accepted{}, H.Finalized{xs, p}, H.Clears{}, H.Complete{next}, H.Normal{}}) == H.Executed{r, ctx, xs, p, H.Complete{next}} : H.Branch}
    %Equal.sym(Input.PreAuthentication, Input.decode(bs, S.schema(c), S.limits(c)), Input.InputReady{s, r}, decoded) :
      {H.decide_pre(_, H.DataTools{H.Accepted{}, H.Finalized{xs, p}, H.Clears{}, H.Complete{next}, H.Normal{}}) == H.Executed{r, ctx, xs, p, H.Complete{next}} : H.Branch}
    %Equal.sym(Maybe<&2, D.Context>, D.authenticate(s, I.credential(r)), Some{ctx}, authenticated) :
      {H.decide_identity(_, r, H.DataTools{H.Accepted{}, H.Finalized{xs, p}, H.Clears{}, H.Complete{next}, H.Normal{}}) == H.Executed{r, ctx, xs, p, H.Complete{next}} : H.Branch}
    {==}))

def apply_return_value_of_ready(~source: Source.Source, ~c: S.Configuration, +origin: Source.JudgmentSyntactic,
  +s: D.State, +r: P.Request, +ctx: D.Context, +data: H.DataTools,
  returns: ReturnsInPre(source, c, origin, data, Input.InputReady{s, r}),
  authenticated: {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>}) ->
  L.E<Source.JudgmentClientReal(source, c, r, ctx, origin, H.judgment_of(data)), NativeReturnValue(source, c, origin, s, r, ctx, output(data), cleanup(data))>:
  returns(ctx, authenticated)

def returns_of_request(~source: Source.Source, ~c: S.Configuration, +origin: Source.JudgmentSyntactic,
  +s: D.State, +input: X.Reception, +be: List<&2, U32>, +br: List<&2, U32>, +bs: List<&2, U32>,
  +r: P.Request, +ctx: D.Context, +data: H.DataTools,
  received: {X.decide_reception(c, input) == X.ProcessBody{br} : X.Disposition},
  assembly_result: {Transport.join(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>},
  decoded: {Input.decode(bs, S.schema(c), S.limits(c)) == Input.InputReady{s, r} : Input.PreAuthentication},
  authenticated: {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>},
  returns: ReturnsInDisposition(source, c, origin, be, data, X.decide_reception(c, input))) ->
  L.E<Source.JudgmentClientReal(source, c, r, ctx, origin, H.judgment_of(data)), NativeReturnValue(source, c, origin, s, r, ctx, output(data), cleanup(data))>:
  apply_return_value_of_ready(source, c, origin, s, r, ctx, data,
    (%decoded : ReturnsInPre(source, c, origin, data, _)
      %assembly_result : ReturnsInPacket(source, c, origin, data, _)
      %received : ReturnsInDisposition(source, c, origin, be, data, _) returns), authenticated)

def AdmittedInTrace(~source: Source.Source, +origin: Source.JudgmentSyntactic, -p: S.Program,
  -qs: List<&2, Q.Frame>, +r: P.Request, +ctx: D.Context) -> Type:
  L.E<{p == Source.program(source, origin) : S.Program}, L.E<ExistsFrame(qs, Q.Accepts{r, ctx}), ExistsFrame(qs, Q.Started{r, ctx})>>

def milestones_combined_return(~source: Source.Source, ~c: S.Configuration, +origin: Source.JudgmentSyntactic,
  +m: H.Micro, +world: Nat, +s: D.State, +input: X.Reception, +be: List<&2, U32>,
  +r: P.Request, +ctx: D.Context, -p: S.Program, +br: List<&2, U32>, +bs: List<&2, U32>,
  +j: H.Judgment, +ex: H.OutputExecution, +li: H.Cleanup, +en: H.Delivery, +pre: H.Preprocessing, +next: Bool,
  received: {X.decide_reception(c, input) == X.ProcessBody{br} : X.Disposition},
  assembly_result: {Transport.join(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>},
  decoded: {Input.decode(bs, S.schema(c), S.limits(c)) == Input.InputReady{s, r} : Input.PreAuthentication},
  authenticated: {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>},
  normal: {pre == H.Normal{} : H.Preprocessing}, write: {en == H.Complete{next} : H.Delivery},
  gate: L.E<{j == H.Accepted{} : H.Judgment}, L.E<{p == Source.program(source, origin) : S.Program}, NativeReturn(ex, li)>>) ->
  AdmittedInTrace(source, origin, p, H.render(m, s, H.decide(c, input, be, H.DataTools{j, ex, li, en, pre})), r, ctx):
  match gate:
    case L.Both{accepted, L.Both{same_program, (+xs, +prepared, L.Both{executed, cleared})}}:
      %Equal.sym(H.Branch, H.decide(c, input, be, H.DataTools{j, ex, li, en, pre}), H.Executed{r, ctx, xs, prepared, H.Complete{next}},
        branch_executed(c, input, be, H.DataTools{j, ex, li, en, pre}, s, r, ctx, br, bs, xs, prepared, next,
          tools_exact(j, ex, li, en, pre, xs, prepared, next, accepted, executed, cleared, write, normal), received, assembly_result, decoded, authenticated)) :
          AdmittedInTrace(source, origin, p, H.render(m, s, _), r, ctx)
      L.Both{same_program, milestones_of_execution(m, s, r, ctx, xs, prepared, next)}

def admission_of_assembly(~source: Source.Source, ~c: S.Configuration, +origin: Source.JudgmentSyntactic,
  +m: H.Micro, +world: Nat, +s: D.State, +input: X.Reception, +be: List<&2, U32>,
  +r: P.Request, +ctx: D.Context, p: S.Program, +br: List<&2, U32>, +bs: List<&2, U32>,
  +j: H.Judgment, +ex: H.OutputExecution, +li: H.Cleanup, +en: H.Delivery, +pre: H.Preprocessing, +next: Bool,
  +received: {X.decide_reception(c, input) == X.ProcessBody{br} : X.Disposition},
  +assembly_result: {Transport.join(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>},
  +decoded: {Input.decode(bs, S.schema(c), S.limits(c)) == Input.InputReady{s, r} : Input.PreAuthentication},
  +authenticated: {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>},
  normal: {pre == H.Normal{} : H.Preprocessing}, write: {en == H.Complete{next} : H.Delivery}, terminated: JudgmentTerminated(j),
  returns: ReturnsInDisposition(source, c, origin, be, H.DataTools{j, ex, li, en, pre}, X.decide_reception(c, input)),
  functional: ElaborationFunctional(source, c), certificate: L.E<I.Bound(Source.environment(source), c, I.code(r), p),
    I.Derives(Source.environment(source), c, I.proof(r), R.Certifies(c, I.code(r), p, ctx, I.arguments(r)))>) ->
  AdmittedInTrace(source, origin, p, H.render(m, s, H.decide(c, input, be, H.DataTools{j, ex, li, en, pre})), r, ctx):
  F.combined_pair(AdmittedInTrace(source, origin, p, H.render(m, s, H.decide(c, input, be, H.DataTools{j, ex, li, en, pre})), r, ctx),
    Source.JudgmentClientReal(source, c, r, ctx, origin, j), NativeReturnValue(source, c, origin, s, r, ctx, ex, li),
    returns_of_request(source, c, origin, s, input, be, br, bs, r, ctx, H.DataTools{j, ex, li, en, pre}, received, assembly_result, decoded, authenticated, returns),
    checked => runtime => milestones_combined_return(source, c, origin, m, world, s, input, be, r, ctx, p, br, bs, j, ex, li, en, pre, next,
      received, assembly_result, decoded, authenticated, normal, write, gate_admits_certificate(source, c, origin, s, r, ctx, p, j, ex, li, terminated, checked, runtime, functional, certificate)))

def PacketOfRequest(~c: S.Configuration, +s: D.State, +input: X.Reception, +be: List<&2, U32>, +r: P.Request) -> Type:
  &br: List<&2, U32> -> &bs: List<&2, U32> -> L.E<{X.decide_reception(c, input) == X.ProcessBody{br} : X.Disposition},
    L.E<{Transport.join(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>},
      {Input.decode(bs, S.schema(c), S.limits(c)) == Input.InputReady{s, r} : Input.PreAuthentication}>>

def admission_combined_packet(~source: Source.Source, ~c: S.Configuration, +origin: Source.JudgmentSyntactic,
  +m: H.Micro, +world: Nat, +s: D.State, +input: X.Reception, +be: List<&2, U32>, +data: H.DataTools,
  +r: P.Request, +ctx: D.Context, p: S.Program, packet: PacketOfRequest(c, s, input, be, r),
  available: ToolsAvailable(source, c, origin, be, input, data), functional: ElaborationFunctional(source, c),
  authenticated: {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>},
  certificate: L.E<I.Bound(Source.environment(source), c, I.code(r), p),
    I.Derives(Source.environment(source), c, I.proof(r), R.Certifies(c, I.code(r), p, ctx, I.arguments(r)))>) ->
  AdmittedInTrace(source, origin, p, H.render(m, s, H.decide(c, input, be, data)), r, ctx):
  match data:
    case H.DataTools{+j, +ex, +li, +en, +pre}:
      match packet:
        case (+br, +bs, L.Both{received, L.Both{assembly_result, decoded}}):
          match available:
            case L.Both{normal, L.Both{(+next, write), L.Both{terminated, returns}}}:
              admission_of_assembly(source, c, origin, m, world, s, input, be, r, ctx, p, br, bs, j, ex, li, en, pre, next,
                received, assembly_result, decoded, authenticated, normal, write, terminated, returns, functional, certificate)

def AdmissionOfCall(~source: Source.Source, ~c: S.Configuration, +s: D.State, +input: X.Reception,
  data: Source.CallData, -p: S.Program, +r: P.Request, +ctx: D.Context) -> Type:
  match data:
    case Source.CallData{cf, origin, pf, tf, be, tools, micro}:
      AdmittedInTrace(source, origin, p, H.render(micro, s, H.decide(c, input, be, tools)), r, ctx)

def CopyOfState(~c: S.Configuration, +s: D.State, data: Source.CallData) -> Type:
  match data:
    case Source.CallData{cf, origin, pf, tf, be, tools, micro}: Copy.StateCopied(c, s, be)

def admission_of_metadata(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +input: X.Reception,
  data: Source.CallData, +r: P.Request, +ctx: D.Context, p: S.Program,
  copied: CopyOfState(c, s, data), body: Copy.BodyCopied(c, input), structure: {D.structure(S.schema(c), s) == True{} : Bool},
  available: AvailabilityOfCall(source, c, input, data), functional: ElaborationFunctional(source, c),
  received: I.RequestReceived(I.Serve{world, c, s, input}, r),
  authenticated: {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>},
  certificate: L.E<I.Bound(Source.environment(source), c, I.code(r), p),
    I.Derives(Source.environment(source), c, I.proof(r), R.Certifies(c, I.code(r), p, ctx, I.arguments(r)))>) ->
  AdmissionOfCall(source, c, s, input, data, p, r, ctx):
  match data:
    case Source.CallData{cf, +origin, pf, tf, +be, +tools, +micro}:
      admission_combined_packet(source, c, origin, micro, world, s, input, be, tools, r, ctx, p,
        packet_of_request_received(c, world, s, input, be, r, copied, body, structure, received), available, functional, authenticated, certificate)

def admission_in_source(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +input: X.Reception,
  +data: Source.CallData, +same: {data == Source.call(source, world) : Source.CallData},
  +r: P.Request, +ctx: D.Context, -p: S.Program,
  canonical: {I.Serve{world, c, s, input} == Source.scenario(source, world) : I.Scenario},
  admitted: AdmissionOfCall(source, c, s, input, data, p, r, ctx)) ->
  L.E<I.InSomeMoment(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, input}, I.CertificateAccepted{r, ctx, p}),
    I.InSomeMoment(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, input}, I.ProgramStarted{r, ctx, p})>:
  match data:
    case Source.CallData{+cf, +origin, +pf, +tf, +be, +tools, +micro}:
      match admitted:
        case L.Both{same_program, L.Both{(+ta, accepted), (+tc, started)}}:
          %Equal.sym(S.Program, p, Source.program(source, origin), same_program) :
            L.E<I.InSomeMoment(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, input}, I.CertificateAccepted{r, ctx, _}),
              I.InSomeMoment(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, input}, I.ProgramStarted{r, ctx, _})>
          F.combined_pair(
            L.E<I.InSomeMoment(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, input}, I.CertificateAccepted{r, ctx, Source.program(source, origin)}),
              I.InSomeMoment(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, input}, I.ProgramStarted{r, ctx, Source.program(source, origin)})>,
            {I.Serve{world, c, s, input} == Source.scenario(source, world) : I.Scenario},
            {I.Serve{world, c, s, input} == Source.scenario(source, world) : I.Scenario},
            Call.duplicate_equality(I.Scenario, I.Serve{world, c, s, input}, Source.scenario(source, world), canonical), c1 => c2 => L.Both{
              (ta, event_of_route(source, c, Source.Service{world, s, input}, ta, Q.Accepts{r, ctx}, I.CertificateAccepted{r, ctx, Source.program(source, origin)}, c1, Unit{},
                (%same : RelationOfOrigin(source, c, origin_of_observation(Source.construct_call(c, s, input, _)), Q.Accepts{r, ctx}, I.CertificateAccepted{r, ctx, Source.program(source, origin)}) {==}),
                (%same : {Q.query(frames(Source.construct_call(c, s, input, _)), ta) == Some{Q.Accepts{r, ctx}} : Maybe<&2, Q.Frame>} accepted))),
              (tc, event_of_route(source, c, Source.Service{world, s, input}, tc, Q.Started{r, ctx}, I.ProgramStarted{r, ctx, Source.program(source, origin)}, c2, Unit{},
                (%same : RelationOfOrigin(source, c, origin_of_observation(Source.construct_call(c, s, input, _)), Q.Started{r, ctx}, I.ProgramStarted{r, ctx, Source.program(source, origin)}) {==}),
                (%same : {Q.query(frames(Source.construct_call(c, s, input, _)), tc) == Some{Q.Started{r, ctx}} : Maybe<&2, Q.Frame>} started)))})

# Both instances are logical evidence of the same fixed results.
# They neither rerun checker/worker nor duplicate the linear program.
def PrimitivesService(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +input: X.Reception) -> Type:
  L.E<AvailabilityOfCall(source, c, input, Source.call(source, world)),
    L.E<AvailabilityOfCall(source, c, input, Source.call(source, world)),
      L.E<CopyOfState(c, s, Source.call(source, world)),
        L.E<Copy.BodyCopied(c, input), ElaborationFunctional(source, c)>>>>

def ResultService(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +input: X.Reception) -> Type:
  L.E<K.ServiceTerminates(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, input}),
    @r: P.Request -> @ctx: D.Context -> @p: S.Program ->
      I.RequestReceived(I.Serve{world, c, s, input}, r) ->
      {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>} ->
      L.E<I.Bound(Source.environment(source), c, I.code(r), p),
        I.Derives(Source.environment(source), c, I.proof(r), R.Certifies(c, I.code(r), p, ctx, I.arguments(r)))> ->
        L.E<I.InSomeMoment(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, input}, I.CertificateAccepted{r, ctx, p}),
          I.InSomeMoment(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, input}, I.ProgramStarted{r, ctx, p})>>

def structure_of_state(c: S.Configuration, +s: D.State, structure: {R.structure(c, s) == True{} : Bool}) ->
  {D.structure(S.schema(c), s) == True{} : Bool}:
  match c:
    case S.Configuration{+e, ls, +lim, amb}:
      F.and_boolean_left(D.structure(e, s), R.fits(R.limit_state(lim), D.state_value(s)), structure)

def service_primitive(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +input: X.Reception,
  canonical: {I.Serve{world, c, s, input} == Source.scenario(source, world) : I.Scenario},
  configuration: I.ConfigurationValid(Source.environment(source), c), valid: R.Valid(c, s), primitives: PrimitivesService(source, c, world, s, input)) ->
  ResultService(source, c, world, s, input):
  match configuration valid primitives:
    case L.Both{cfg, id} L.Both{structure, laws} L.Both{end, L.Both{admission, L.Both{copied, L.Both{body, functional}}}}:
      F.combined_pair(ResultService(source, c, world, s, input),
        {I.Serve{world, c, s, input} == Source.scenario(source, world) : I.Scenario},
        {I.Serve{world, c, s, input} == Source.scenario(source, world) : I.Scenario},
        Call.duplicate_equality(I.Scenario, I.Serve{world, c, s, input}, Source.scenario(source, world), canonical), c1 => c2 => L.Both{
          terminate_of_source(source, c, world, s, input, c1,
            end_of_call(source, c, world, s, input, Source.call(source, world), {==}, Preparation.limits_of_configuration(c, cfg), end)),
          +r => +ctx => p => received => authenticated => certificate =>
            admission_in_source(source, c, world, s, input, Source.call(source, world), {==}, r, ctx, p, c2,
              admission_of_metadata(source, c, world, s, input, Source.call(source, world), r, ctx, p,
                copied, body, structure_of_state(c, s, structure), admission, functional, received, authenticated, certificate))})

# Initialization uses only actual checker/worker approval and return.
def PrimitivesInitial(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +pi: String) -> Type:
  I.Derives(Source.environment(source), c, pi, R.Valid(c, s)) ->
    &cf: Source.JudgmentSyntactic -> &sf: Source.JudgmentSyntactic -> &pf: Source.JudgmentSyntactic -> &micro: H.Micro ->
      {Source.initial(source, world) == Source.InitialData{cf, sf, pf, H.Accepted{}, H.InitializationFinished{}, micro} : Source.InitialData}

def start_primitive_result(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +pi: String,
  canonical: {I.Initialize{world, c, s, pi} == Source.scenario(source, world) : I.Scenario},
  configured: {Config.is_valid(c, Source.identity(source)) == True{} : Bool}, valid: R.Valid(c, s),
  result: &cf: Source.JudgmentSyntactic -> &sf: Source.JudgmentSyntactic -> &pf: Source.JudgmentSyntactic -> &micro: H.Micro ->
    {Source.initial(source, world) == Source.InitialData{cf, sf, pf, H.Accepted{}, H.InitializationFinished{}, micro} : Source.InitialData}) ->
  I.InSomeMoment(Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, I.InstanceStarted{s}):
  match result:
    case (+cf, +sf, +pf, +micro, origin):
      Source.initialization_approved_reaches_start(source, c, world, s, pi, cf, sf, pf, micro, canonical, origin, configured, valid)

def initial_primitive(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +pi: String,
  canonical: {I.Initialize{world, c, s, pi} == Source.scenario(source, world) : I.Scenario},
  conditions: K.InitializationPossible(Source.environment(source), c, s, pi), primitives: PrimitivesInitial(source, c, world, s, pi)) ->
  I.InSomeMoment(Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, I.InstanceStarted{s}):
  match conditions:
    case L.Both{configuration, L.Both{derived, valid}}:
      start_primitive_result(source, c, world, s, pi, canonical,
        Configuration.configuration_original_is_valid_and_accepts(Source.environment(source), c, configuration), valid, primitives(derived))

# Separates Law8 conditions and consequence while preserving its definition.
def Conditions(~source: Source.Source, x: I.Scenario) -> Type:
  match x:
    case I.Initialize{m, c, s, pi}: K.InitializationPossible(Source.environment(source), c, s, pi)
    case I.Serve{m, c, s, input}: L.E<I.ConfigurationValid(Source.environment(source), c), L.E<R.Valid(c, s), X.ReceptionValid(input)>>

def Outcome(~source: Source.Source, x: I.Scenario) -> Type:
  match x:
    case I.Initialize{m, c, +s, pi}: I.InSomeMoment(Source.environment(source), Source.artifact(source), I.Initialize{m, c, s, pi}, I.InstanceStarted{s})
    case I.Serve{+m, c, +s, +input}:
      L.E<K.ServiceTerminates(Source.environment(source), Source.artifact(source), I.Serve{m, c, s, input}),
        @r: P.Request -> @ctx: D.Context -> @p: S.Program ->
          I.RequestReceived(I.Serve{m, c, s, input}, r) ->
          {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>} ->
          L.E<I.Bound(Source.environment(source), c, I.code(r), p),
            I.Derives(Source.environment(source), c, I.proof(r), R.Certifies(c, I.code(r), p, ctx, I.arguments(r)))> ->
              L.E<I.InSomeMoment(Source.environment(source), Source.artifact(source), I.Serve{m, c, s, input}, I.CertificateAccepted{r, ctx, p}),
                I.InSomeMoment(Source.environment(source), Source.artifact(source), I.Serve{m, c, s, input}, I.ProgramStarted{r, ctx, p})>>

def PrimitivesOfContext(~source: Source.Source, ~c: S.Configuration, x: Source.Context) -> Type:
  match x:
    case Source.Initial{+m, +s, +pi}: PrimitivesInitial(source, c, m, s, pi)
    case Source.Service{+m, +s, +input}: PrimitivesService(source, c, m, s, input)

def progress_in_context(~source: Source.Source, ~c: S.Configuration, +x: Source.Context,
  canonical: {Source.scenario_context(c, x) == Source.scenario(source, Source.world(Source.scenario_context(c, x))) : I.Scenario},
  conditions: Conditions(source, Source.scenario_context(c, x)), primitives: PrimitivesOfContext(source, c, x)) ->
  Outcome(source, Source.scenario_context(c, x)):
  match x:
    case Source.Initial{+m, +s, +pi}: initial_primitive(source, c, m, s, pi, canonical, conditions, primitives)
    case Source.Service{+m, +s, +input}:
      match conditions:
        case L.Both{configuration, L.Both{valid, reception}}: service_primitive(source, c, m, s, input, canonical, configuration, valid, primitives)

def PrimitivesOfModel(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String, +world: Nat) -> Type:
  PrimitivesOfContext(Model.source(base, c, seed, history, moment, pi), c,
    Two.context_of_moment(seed, history, pi, world, moment(world)))

# External availability contract: scenario coherence and primitive
# returns. Processable remains exactly the original predicate.
def AvailabilityOfModel(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String) -> Type:
  @x: I.Scenario -> I.Processable(Source.environment(Model.source(base, c, seed, history, moment, pi)), x) ->
    L.E<{x == Source.scenario(Model.source(base, c, seed, history, moment, pi), Source.world(x)) : I.Scenario},
      PrimitivesOfModel(base, c, seed, history, moment, pi, Source.world(x))>

def progress_by_equality_of_context(~source: Source.Source, ~c: S.Configuration, +world: Nat, +x: Source.Context,
  world_equal: {Source.world(Source.scenario_context(c, x)) == world : Nat},
  equal: {Source.scenario_context(c, x) == Source.scenario(source, world) : I.Scenario},
  conditions: Conditions(source, Source.scenario(source, world)), primitives: PrimitivesOfContext(source, c, x)) ->
  Outcome(source, Source.scenario(source, world)):
  F.combined_pair(Outcome(source, Source.scenario(source, world)),
    {Source.scenario_context(c, x) == Source.scenario(source, world) : I.Scenario},
    {Source.scenario_context(c, x) == Source.scenario(source, world) : I.Scenario},
    Call.duplicate_equality(I.Scenario, Source.scenario_context(c, x), Source.scenario(source, world), equal), i1 => i2 =>
      Five.apply(Conditions(source, Source.scenario(source, world)), Outcome(source, Source.scenario(source, world)),
        (%i1 : Conditions(source, _) -> Outcome(source, _)
          cs => progress_in_context(source, c, x, Two.same_world_of_context(source, c, world, x, world_equal, i2), cs, primitives)), conditions))

def progress_in_canonical(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String, +world: Nat,
  conditions: Conditions(Model.source(base, c, seed, history, moment, pi), Source.scenario(Model.source(base, c, seed, history, moment, pi), world)),
  primitives: PrimitivesOfModel(base, c, seed, history, moment, pi, world)) ->
  Outcome(Model.source(base, c, seed, history, moment, pi), Source.scenario(Model.source(base, c, seed, history, moment, pi), world)):
  progress_by_equality_of_context(Model.source(base, c, seed, history, moment, pi), c, world,
    Two.context_of_moment(seed, history, pi, world, moment(world)),
    Two.context_preserves_world(c, seed, history, pi, world, moment(world)),
    Equal.trans(I.Scenario,
      Source.scenario_context(c, Two.context_of_moment(seed, history, pi, world, moment(world))),
      Scenarios.canonical(c, seed, history, moment, pi, world), Source.scenario(Model.source(base, c, seed, history, moment, pi), world),
      Two.context_represents_scenario(c, seed, history, pi, world, moment(world)),
      Equal.sym(I.Scenario, Source.scenario(Model.source(base, c, seed, history, moment, pi), world), Scenarios.canonical(c, seed, history, moment, pi, world),
        Model.scenario_of_model(base, c, seed, history, moment, pi, world))), conditions, primitives)

def result_after_coherence(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String,
  -x: I.Scenario, +world: Nat,
  conditions: Conditions(Model.source(base, c, seed, history, moment, pi), x),
  origin: L.E<{x == Source.scenario(Model.source(base, c, seed, history, moment, pi), world) : I.Scenario},
    PrimitivesOfModel(base, c, seed, history, moment, pi, world)>) ->
  Outcome(Model.source(base, c, seed, history, moment, pi), x):
  match origin:
    case L.Both{equal, primitives}:
      Five.apply(Conditions(Model.source(base, c, seed, history, moment, pi), x),
        Outcome(Model.source(base, c, seed, history, moment, pi), x),
        (%Equal.sym(I.Scenario, x, Source.scenario(Model.source(base, c, seed, history, moment, pi), world), equal) :
          Conditions(Model.source(base, c, seed, history, moment, pi), _) -> Outcome(Model.source(base, c, seed, history, moment, pi), _)
          cs => progress_in_canonical(base, c, seed, history, moment, pi, world, cs, primitives)), conditions)

def progress_of_scenario(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String,
  availability: AvailabilityOfModel(base, c, seed, history, moment, pi), x: I.Scenario) ->
  K.Progress(x, Source.environment(Model.source(base, c, seed, history, moment, pi)), Source.artifact(Model.source(base, c, seed, history, moment, pi))):
  match x:
    case I.Initialize{+m, original, +s, +proof}:
      possible => processable => result_after_coherence(base, c, seed, history, moment, pi, I.Initialize{m, original, s, proof}, m,
        possible, availability(I.Initialize{m, original, s, proof}, processable))
    case I.Serve{+m, original, +s, +input}:
      configuration => valid => reception => processable =>
        result_after_coherence(base, c, seed, history, moment, pi, I.Serve{m, original, s, input}, m,
          L.Both{configuration, L.Both{valid, reception}}, availability(I.Serve{m, original, s, input}, processable))

# EXACT Law8: receives no Progress, Concluded or Started as a premise.
def law8_of_model(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String,
  availability: AvailabilityOfModel(base, c, seed, history, moment, pi)) ->
  K.Law8(Source.environment(Model.source(base, c, seed, history, moment, pi)), Source.artifact(Model.source(base, c, seed, history, moment, pi))):
  x => progress_of_scenario(base, c, seed, history, moment, pi, availability, x)
