# Channel-closure causes in the generated route and actual IO facts.
import Base
import ../contract/Data.bend as D
import ../contract/Interface.bend as I
import ../contract/LAWS.bend as K
import ../contract/Logic.bend as L
import ../contract/Protocol.bend as P
import ../contract/Resources.bend as X
import ../contract/Semantics.bend as S
import ../src/Core.bend as N
import ../src/Input.bend as Input
import ../src/ConfigurationCheck.bend as Config
import ../src/Transport.bend as Transport
import ./SourceService.bend as Source
import ./ProtocolService.bend as Q
import ./RoutesService.bend as R
import ./PrimitivesService.bend as M
import ./Law5Service.bend as Five
import ./Law34Service.bend as Adm
import ./LinkageService.bend as Linkage
import ./VisibilityService.bend as Vis
import ./Foundations.bend as F

# These are actual external effects by occurrence, not responses/laws.
def FailuresReal(~source: Source.Source, -x: I.Scenario, -qs: List<&2, Q.Frame>) -> Type:
  @t: Nat -> @stage: X.Stage -> @id: String -> @fatal: Bool ->
    {Q.query(qs, t) == Some{Q.Failed{stage, id, fatal}} : Maybe<&2, Q.Frame>} ->
      I.FailureReal(Source.environment(source), Source.artifact(source), x, t, stage, id, fatal)

def FailuresOfDeliveryReal(~source: Source.Source, -x: I.Scenario, -qs: List<&2, Q.Frame>) -> Type:
  @t: Nat -> @prefix: List<&2, U32> -> {Q.query(qs, t) == Some{Q.Interrupted{prefix}} : Maybe<&2, Q.Frame>} ->
    I.FailureDeliveryReal(Source.environment(source), Source.artifact(source), x, t)

def closed(q: Q.Frame) -> Bool:
  match q:
    case Q.Closed{}: True{}
    case _: False{}

def NotClose(-qs: List<&2, Q.Frame>) -> Type:
  Five.WithoutFrame(qs, Q.Closed{})

def empty() -> NotClose(Nil{}):
  Five.empty_without_frame(Q.Closed{})

def front(+q: Q.Frame, -qs: List<&2, Q.Frame>, neutral: {closed(q) == False{} : Bool}, rest: NotClose(qs)) -> NotClose(Con{q, qs}):
  Five.head_by_tag(closed, q, Q.Closed{}, qs, neutral, {==}, rest)

def concatenate(+xs: List<&2, Q.Frame>, -ys: List<&2, Q.Frame>, a: NotClose(xs), b: NotClose(ys)) -> NotClose(Q.concatenate(xs, ys)):
  Five.concatenate_without_frame(xs, ys, Q.Closed{}, a, b)

def micro_input(m: R.Micro) -> NotClose(R.micro_input(m)):
  match m:
    case R.Micro{+a, b, c, d}: Five.internal_negative_contains(M.expand_primitives(a), Q.Closed{}, M.primitives_only_generate_internal(a), {==})
def micro_auth(m: R.Micro) -> NotClose(R.micro_authentication(m)):
  match m:
    case R.Micro{a, +b, c, d}: Five.internal_negative_contains(M.expand_primitives(b), Q.Closed{}, M.primitives_only_generate_internal(b), {==})
def micro_exec(m: R.Micro) -> NotClose(R.micro_execution(m)):
  match m:
    case R.Micro{a, b, +c, d}: Five.internal_negative_contains(M.expand_primitives(c), Q.Closed{}, M.primitives_only_generate_internal(c), {==})
def micro_output(m: R.Micro) -> NotClose(R.micro_output(m)):
  match m:
    case R.Micro{a, b, c, +d}: Five.internal_negative_contains(M.expand_primitives(d), Q.Closed{}, M.primitives_only_generate_internal(d), {==})

def received(+m: R.Micro, +r: P.Request) -> NotClose(R.render_received(m, r)):
  concatenate(R.micro_input(m), [Q.Received{r}], micro_input(m), front(Q.Received{r}, Nil{}, {==}, empty()))
def authenticated(+m: R.Micro, +r: P.Request, +ctx: D.Context) -> NotClose(R.render_authenticated(m, r, ctx)):
  concatenate(R.render_received(m, r), Q.concatenate(R.micro_authentication(m), [Q.Authenticated{r, Some{ctx}}]), received(m, r),
    concatenate(R.micro_authentication(m), [Q.Authenticated{r, Some{ctx}}], micro_auth(m), front(Q.Authenticated{r, Some{ctx}}, Nil{}, {==}, empty())))
def verified(+m: R.Micro, +r: P.Request, +ctx: D.Context) -> NotClose(R.render_verified(m, r, ctx)):
  concatenate(R.render_authenticated(m, r, ctx), [Q.Accepts{r, ctx}], authenticated(m, r, ctx), front(Q.Accepts{r, ctx}, Nil{}, {==}, empty()))
def started(+m: R.Micro, +r: P.Request, +ctx: D.Context) -> NotClose(R.render_started(m, r, ctx)):
  concatenate(R.render_verified(m, r, ctx), Q.concatenate(R.micro_execution(m), [Q.Started{r, ctx}]), verified(m, r, ctx),
    concatenate(R.micro_execution(m), [Q.Started{r, ctx}], micro_exec(m), front(Q.Started{r, ctx}, Nil{}, {==}, empty())))
def frames_exec(+r: P.Request, +ctx: D.Context, xs: List<&2, Q.FrameExec>) -> NotClose(Q.expand_exec(r, ctx, xs)):
  match xs:
    case Nil{}: empty()
    case Con{Q.Evaluation{+p}, t}: front(Q.Evaluated{r, ctx, p}, Q.expand_exec(r, ctx, t), {==}, frames_exec(r, ctx, t))
    case Con{Q.Operation{+e, +s, +o, +res}, t}: front(Q.Operated{e, s, o, res}, Q.expand_exec(r, ctx, t), {==}, frames_exec(r, ctx, t))
def execution(+m: R.Micro, +r: P.Request, +ctx: D.Context, +xs: List<&2, Q.FrameExec>) -> NotClose(R.render_execution(m, r, ctx, xs)):
  concatenate(R.render_started(m, r, ctx), Q.expand_exec(r, ctx, xs), started(m, r, ctx), frames_exec(r, ctx, xs))
def prepared(p: N.Prepared) -> {closed(R.frame_prepared(p)) == False{} : Bool}:
  match p:
    case N.Prepared{w, ts, r, bs}: {==}
def phase(+m: R.Micro, f: R.PhaseBefore) -> NotClose(R.render_phase(m, f)):
  match f:
    case R.BeforeInput{}: micro_input(m)
    case R.AfterReceive{+r}: received(m, r)
    case R.AfterAuthenticate{+r, +ctx}: authenticated(m, r, ctx)
    case R.AfterVerify{+r, +ctx}: verified(m, r, ctx)
    case R.Executing{+r, +ctx, +xs}: execution(m, r, ctx, xs)
    case R.AfterPrepare{+r, +ctx, +xs, +p}:
      concatenate(R.render_execution(m, r, ctx, xs), Q.concatenate(R.micro_output(m), [R.frame_prepared(p)]), execution(m, r, ctx, xs),
        concatenate(R.micro_output(m), [R.frame_prepared(p)], micro_output(m), front(R.frame_prepared(p), Nil{}, prepared(p), empty())))

# The preceding three causes query the SAME list; the fourth cause
# is the WithoutResponse disposition, whose selector origin is proved later.
def Cause(-xs: List<&2, Q.Frame>, -t: Nat, -branch: R.Branch) -> Type:
  L.Disjunction<{branch == R.WithoutResponse{} : R.Branch},
    L.Disjunction<&stage: X.Stage -> &id: String -> Adm.Before(xs, t, Q.Failed{stage, id, True{}}),
      L.Disjunction<&r: S.Response -> &s: D.State -> Adm.Before(xs, t, Q.Completed{r, s, True{}}),
        &bs: List<&2, U32> -> Adm.Before(xs, t, Q.Interrupted{bs})>>>

def before_shifted(+xs: List<&2, Q.Frame>, +ys: List<&2, Q.Frame>, +t: Nat, -q: Q.Frame, before: Adm.Before(ys, t, q)) -> Adm.Before(Q.concatenate(xs, ys), Nat.add(Q.size(xs), t), q):
  match before:
    case (+u, L.Both{order, query_result}): (Nat.add(Q.size(xs), u), L.Both{Q.order_shifted(Q.size(xs), u, t, order),
      Equal.trans(Maybe<&2, Q.Frame>, Q.query(Q.concatenate(xs, ys), Nat.add(Q.size(xs), u)), Q.query(ys, u), Some{q}, Q.query_after_prefix(xs, ys, u), query_result)})

def cause_shifted(+xs: List<&2, Q.Frame>, +ys: List<&2, Q.Frame>, +t: Nat, -branch: R.Branch, cause: Cause(ys, t, branch)) -> Cause(Q.concatenate(xs, ys), Nat.add(Q.size(xs), t), branch):
  match cause:
    case L.Left{without}: L.Left{without}
    case L.Right{L.Left{(stage, id, before)}}: L.Right{L.Left{(stage, id, before_shifted(xs, ys, t, Q.Failed{stage, id, True{}}, before))}}
    case L.Right{L.Right{L.Left{(r, s, before)}}}: L.Right{L.Right{L.Left{(r, s, before_shifted(xs, ys, t, Q.Completed{r, s, True{}}, before))}}}
    case L.Right{L.Right{L.Right{(bs, before)}}}: L.Right{L.Right{L.Right{(bs, before_shifted(xs, ys, t, Q.Interrupted{bs}, before))}}}

def cause_in_suffix(+xs: List<&2, Q.Frame>, +ys: List<&2, Q.Frame>, -branch: R.Branch, +t: Nat,
  cause: @u: Nat -> {Q.query(ys, u) == Some{Q.Closed{}} : Maybe<&2, Q.Frame>} -> Cause(ys, u, branch),
  part: &u: Nat -> L.E<{t == Nat.add(Q.size(xs), u) : Nat}, {Q.query(ys, u) == Some{Q.Closed{}} : Maybe<&2, Q.Frame>}>) -> Cause(Q.concatenate(xs, ys), t, branch):
  match part:
    case (+u, L.Both{position, query_result}):
      %Equal.sym(Nat, t, Nat.add(Q.size(xs), u), position) : Cause(Q.concatenate(xs, ys), _, branch)
      cause_shifted(xs, ys, u, branch, cause(u, query_result))

def prefix_cause(+xs: List<&2, Q.Frame>, +ys: List<&2, Q.Frame>, -branch: R.Branch, +t: Nat, without: NotClose(xs),
  cause: @u: Nat -> {Q.query(ys, u) == Some{Q.Closed{}} : Maybe<&2, Q.Frame>} -> Cause(ys, u, branch),
  query_result: {Q.query(Q.concatenate(xs, ys), t) == Some{Q.Closed{}} : Maybe<&2, Q.Frame>}) -> Cause(Q.concatenate(xs, ys), t, branch):
  cause_in_suffix(xs, ys, branch, t, cause, Five.remove_prefix_without_frame(xs, ys, t, Q.Closed{}, without, query_result))

def Causes(-xs: List<&2, Q.Frame>, -branch: R.Branch) -> Type:
  @t: Nat -> {Q.query(xs, t) == Some{Q.Closed{}} : Maybe<&2, Q.Frame>} -> Cause(xs, t, branch)

def swap_causes(-xs: List<&2, Q.Frame>, -ys: List<&2, Q.Frame>, -branch: R.Branch,
  equal: {xs == ys : List<&2, Q.Frame>}, proof: Causes(xs, branch)) -> Causes(ys, branch):
  %equal : Causes(_, branch) proof

def prefix(+xs: List<&2, Q.Frame>, +ys: List<&2, Q.Frame>, -branch: R.Branch, without: NotClose(xs), proof: Causes(ys, branch)) -> Causes(Q.concatenate(xs, ys), branch):
  +t => query_result => prefix_cause(xs, ys, branch, t, without, proof, query_result)

def without_closure(+xs: List<&2, Q.Frame>, -branch: R.Branch, without: NotClose(xs)) -> Causes(xs, branch):
  +t => query_result => L.ex_false(Cause(xs, t, branch), without(t, query_result))

def pair_precedes(+q: Q.Frame, t: Nat, negative_closes: {closed(q) == False{} : Bool},
  query_result: {Q.query([q, Q.Closed{}], t) == Some{Q.Closed{}} : Maybe<&2, Q.Frame>}) -> Adm.Before([q, Q.Closed{}], t, q):
  match t:
    case 0n: L.ex_false(Adm.Before([q, Q.Closed{}], 0n, q), front(q, Nil{}, negative_closes, empty())(0n, query_result))
    case 1n: (0n, L.Both{{==}, {==}})
    case 2n+k: L.ex_false(Adm.Before([q, Q.Closed{}], 2n+k, q), F.none_negative_some(Q.Frame, Q.Closed{}, query_result))

def pair_fatal(+stage: X.Stage, +id: String, -branch: R.Branch) -> Causes([Q.Failed{stage, id, True{}}, Q.Closed{}], branch):
  +t => query_result => L.Right{L.Left{(stage, id, pair_precedes(Q.Failed{stage, id, True{}}, t, {==}, query_result))}}

def pair_interrupted(+bs: List<&2, U32>, -branch: R.Branch) -> Causes([Q.Interrupted{bs}, Q.Closed{}], branch):
  +t => query_result => L.Right{L.Right{L.Right{(bs, pair_precedes(Q.Interrupted{bs}, t, {==}, query_result))}}}

def before_of_all_suffix(+xs: List<&2, Q.Frame>, -ys: List<&2, Q.Frame>, -t: Nat, +j: Nat, -q: Q.Frame, +i: Nat,
  position: {t == Nat.add(Q.size(xs), j) : Nat}, present: {Q.query(xs, i) == Some{q} : Maybe<&2, Q.Frame>}) -> Adm.Before(Q.concatenate(xs, ys), t, q):
  F.combined_pair(Adm.Before(Q.concatenate(xs, ys), t, q), {Q.query(xs, i) == Some{q} : Maybe<&2, Q.Frame>}, {Q.query(xs, i) == Some{q} : Maybe<&2, Q.Frame>},
    Q.equality_reopenable(Maybe<&2, Q.Frame>, Q.query(xs, i), Some{q}, present), one => two =>
      (i, L.Both{(%Equal.sym(Nat, t, Nat.add(Q.size(xs), j), position) : {Nat.is_lt(i, _) == True{} : Bool}
        Five.less_remains_combined_addition(i, Q.size(xs), j, Q.position_present_inside(xs, i, q, one))), Adm.query_prefix(xs, ys, i, q, two)}))

def conclusion_precedes_in_part(+xs: List<&2, Q.Frame>, -ys: List<&2, Q.Frame>, -t: Nat, -branch: R.Branch,
  +r: S.Response, +s: D.State, +i: Nat, present: {Q.query(xs, i) == Some{Q.Completed{r, s, True{}}} : Maybe<&2, Q.Frame>},
  part: &u: Nat -> L.E<{t == Nat.add(Q.size(xs), u) : Nat}, {Q.query(ys, u) == Some{Q.Closed{}} : Maybe<&2, Q.Frame>}>) -> Cause(Q.concatenate(xs, ys), t, branch):
  match part:
    case (+u, L.Both{position, query_result}): L.Right{L.Right{L.Left{(r, s,
      before_of_all_suffix(xs, ys, t, u, Q.Completed{r, s, True{}}, i, position, present))}}}

def part_impossible(-xs: List<&2, Q.Frame>, -ys: List<&2, Q.Frame>, -t: Nat, without: NotClose(ys),
  part: &u: Nat -> L.E<{t == Nat.add(Q.size(xs), u) : Nat}, {Q.query(ys, u) == Some{Q.Closed{}} : Maybe<&2, Q.Frame>}>) -> Empty:
  match part:
    case (u, L.Both{position, query_result}): without(u, query_result)

def later_false_without_close(+s: D.State, next: Bool) -> NotClose(R.later_delivery(False{}, s, next)):
  match next:
    case False{}: empty()
    case True{}: front(Q.Next{s, s}, Nil{}, {==}, empty())

def cause_of_delivery(+xs: List<&2, Q.Frame>, +s: D.State, +r: S.Response, +bs: List<&2, U32>, delivery: R.Delivery, +closes: Bool, +t: Nat, -branch: R.Branch,
  +i: Nat, concluded: {Q.query(xs, i) == Some{Q.Completed{r, s, closes}} : Maybe<&2, Q.Frame>},
  part: &u: Nat -> L.E<{t == Nat.add(Q.size(xs), u) : Nat}, {Q.query(R.render_delivery(s, bs, closes, delivery), u) == Some{Q.Closed{}} : Maybe<&2, Q.Frame>}>) -> Cause(Q.concatenate(xs, R.render_delivery(s, bs, closes, delivery)), t, branch):
  match delivery:
    case R.Complete{+next}:
      match closes:
        case True{}: conclusion_precedes_in_part(xs, R.render_delivery(s, bs, True{}, R.Complete{next}), t, branch, r, s, i, concluded, part)
        case False{}: L.ex_false(Cause(Q.concatenate(xs, R.render_delivery(s, bs, False{}, R.Complete{next})), t, branch),
          part_impossible(xs, R.render_delivery(s, bs, False{}, R.Complete{next}), t, front(Q.Delivered{bs}, R.later_delivery(False{}, s, next), {==}, later_false_without_close(s, next)), part))
    case R.Broken{+prefix}: cause_in_suffix(xs, [Q.Interrupted{prefix}, Q.Closed{}], branch, t, pair_interrupted(prefix, branch), part)
    case R.PendingDelivery{}: L.ex_false(Cause(Q.concatenate(xs, Nil{}), t, branch), part_impossible(xs, Nil{}, t, empty(), part))

def after_conclusion(+before: List<&2, Q.Frame>, +s: D.State, +r: S.Response, +bs: List<&2, U32>, +closes: Bool, +delivery: R.Delivery, -branch: R.Branch,
  without: NotClose(before)) -> Causes(Q.concatenate(Q.concatenate(before, [Q.Completed{r, s, closes}]), R.render_delivery(s, bs, closes, delivery)), branch):
  +t => query_result => cause_of_delivery(Q.concatenate(before, [Q.Completed{r, s, closes}]), s, r, bs, delivery, closes, t, branch,
    Nat.add(Q.size(before), 0n), Adm.query_of_mark(before, Q.Completed{r, s, closes}),
    Five.remove_prefix_without_frame(Q.concatenate(before, [Q.Completed{r, s, closes}]), R.render_delivery(s, bs, closes, delivery), t, Q.Closed{},
      concatenate(before, [Q.Completed{r, s, closes}], without, front(Q.Completed{r, s, closes}, Nil{}, {==}, empty())), query_result))

def publication_without_close(r: S.Response, +s: D.State) -> NotClose(R.render_publication(r, s)):
  match r:
    case S.Response{S.Input{}, v}: empty()
    case S.Response{S.Authentication{}, v}: empty()
    case S.Response{S.Certificate{}, v}: empty()
    case S.Response{S.DataError{}, v}: empty()
    case S.Response{S.Limit{}, v}: empty()
    case S.Response{S.Failure{}, v}: empty()
    case S.Response{S.Refusal{}, v}: empty()
    case S.Response{S.Success{}, v}: front(Q.Published{s}, Nil{}, {==}, empty())

def causes_conclusion(conclusion: N.Conclusion, +closes: Bool, +delivery: R.Delivery, -branch: R.Branch) -> Causes(R.render_conclusion(conclusion, closes, delivery), branch):
  match conclusion:
    case N.Conclusion{+s, +r, +bs}:
      swap_causes(Q.concatenate(Q.concatenate(Con{Q.Prepared{r, bs}, R.render_publication(r, s)}, [Q.Completed{r, s, closes}]), R.render_delivery(s, bs, closes, delivery)),
        R.render_conclusion(N.Conclusion{s, r, bs}, closes, delivery), branch,
        Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, qs => Con{Q.Prepared{r, bs}, qs},
          Q.concatenate(Q.concatenate(R.render_publication(r, s), [Q.Completed{r, s, closes}]), R.render_delivery(s, bs, closes, delivery)),
          Q.concatenate(R.render_publication(r, s), Con{Q.Completed{r, s, closes}, R.render_delivery(s, bs, closes, delivery)}),
          Q.concatenate_assoc(R.render_publication(r, s), [Q.Completed{r, s, closes}], R.render_delivery(s, bs, closes, delivery))),
        after_conclusion(Con{Q.Prepared{r, bs}, R.render_publication(r, s)}, s, r, bs, closes, delivery, branch,
          front(Q.Prepared{r, bs}, R.render_publication(r, s), {==}, publication_without_close(r, s))))

def causes_error_framed(result: Maybe<&2, List<&2, U32>>, +r: S.Response, +s: D.State, +closes: Bool, +delivery: R.Delivery, -branch: R.Branch) -> Causes(R.render_error_framed(result, r, s, closes, delivery), branch):
  match result:
    case None{}: without_closure(Nil{}, branch, empty())
    case Some{+bs}: after_conclusion([Q.Prepared{r, bs}], s, r, bs, closes, delivery, branch, front(Q.Prepared{r, bs}, Nil{}, {==}, empty()))

def causes_error(+status: S.Status, +s: D.State, +closes: Bool, +delivery: R.Delivery, -branch: R.Branch) -> Causes(R.render_error(status, s, closes, delivery), branch):
  causes_error_framed(P.frame(S.response_value(S.response_error(status))), S.response_error(status), s, closes, delivery, branch)

def causes_failure(+s: D.State, +stage: X.Stage, +id: String, fatal: Bool, +delivery: R.Delivery, -branch: R.Branch) -> Causes(R.render_failure(s, stage, id, fatal, delivery), branch):
  match fatal:
    case True{}: pair_fatal(stage, id, branch)
    case False{}: prefix([Q.Failed{stage, id, False{}}], R.render_error(S.Failure{}, s, False{}, delivery), branch,
      front(Q.Failed{stage, id, False{}}, Nil{}, {==}, empty()), causes_error(S.Failure{}, s, False{}, delivery, branch))

def causes_fatal_published(conclusion: N.Conclusion, +stage: X.Stage, +id: String, -branch: R.Branch) -> Causes(R.render_fatal_published(conclusion, stage, id), branch):
  match conclusion:
    case N.Conclusion{+s, +r, +bs}: prefix(Con{Q.Prepared{r, bs}, R.render_publication(r, s)}, [Q.Failed{stage, id, True{}}, Q.Closed{}], branch,
      front(Q.Prepared{r, bs}, R.render_publication(r, s), {==}, publication_without_close(r, s)), pair_fatal(stage, id, branch))

def initial_without_close(q: Maybe<&2, List<&2, U32>>, +s: D.State) -> NotClose(R.render_initial(q, s)):
  match q:
    case None{}: front(Q.Encoded{D.state_value(s), None{}}, Nil{}, {==}, empty())
    case Some{+bs}: front(Q.Encoded{D.state_value(s), Some{bs}}, [Q.Stored{s, bs, s}, Q.Initialized{s}], {==},
      front(Q.Stored{s, bs, s}, [Q.Initialized{s}], {==}, front(Q.Initialized{s}, Nil{}, {==}, empty())))

def prefix_initial_without_close(+m: R.Micro, accepts: Bool) -> NotClose(R.prefix_initial(m, accepts)):
  match accepts:
    case False{}: empty()
    case True{}: front(Q.InitialAccepts{}, R.micro_output(m), {==}, micro_output(m))

def auth_none_without_close(+m: R.Micro, +r: P.Request) -> NotClose(Q.concatenate(R.render_received(m, r), Q.concatenate(R.micro_authentication(m), [Q.Authenticated{r, None{}}]))):
  concatenate(R.render_received(m, r), Q.concatenate(R.micro_authentication(m), [Q.Authenticated{r, None{}}]), received(m, r),
    concatenate(R.micro_authentication(m), [Q.Authenticated{r, None{}}], micro_auth(m), front(Q.Authenticated{r, None{}}, Nil{}, {==}, empty())))

# The renderer root, not an arbitrary list of events.
def causes_without_config(+m: R.Micro, +s: D.State, branch: R.Branch) -> Causes(R.render_branch(m, s, branch), branch):
  match branch:
    case R.InitialOk{}: without_closure(R.render_branch(m, s, R.InitialOk{}), R.InitialOk{},
      front(Q.InitialAccepts{}, Q.concatenate(R.micro_output(m), R.render_initial(P.encode(D.state_value(s)), s)), {==},
        concatenate(R.micro_output(m), R.render_initial(P.encode(D.state_value(s)), s), micro_output(m), initial_without_close(P.encode(D.state_value(s)), s))))
    case R.InitialRefusal{+status}: without_closure([Q.InitialRefused{status}], R.InitialRefusal{status}, front(Q.InitialRefused{status}, Nil{}, {==}, empty()))
    case R.InitialFailure{+accepts, +stage, +id, +fatal}: without_closure(R.render_branch(m, s, R.InitialFailure{accepts, stage, id, fatal}), R.InitialFailure{accepts, stage, id, fatal},
      concatenate(R.prefix_initial(m, accepts), [Q.Failed{stage, id, fatal}, Q.InitialRefused{S.Failure{}}], prefix_initial_without_close(m, accepts),
        front(Q.Failed{stage, id, fatal}, [Q.InitialRefused{S.Failure{}}], {==}, front(Q.InitialRefused{S.Failure{}}, Nil{}, {==}, empty()))))
    case R.WithoutResponse{}: t => query_result => L.Left{{==}}
    case R.InputRefusal{+error, +closes, +delivery}: prefix(R.micro_input(m), R.render_error(R.status_input(error), s, closes, delivery), R.InputRefusal{error, closes, delivery},
      micro_input(m), causes_error(R.status_input(error), s, closes, delivery, R.InputRefusal{error, closes, delivery}))
    case R.AutRefusal{+r, +delivery}:
      swap_causes(Q.concatenate(Q.concatenate(R.render_received(m, r), Q.concatenate(R.micro_authentication(m), [Q.Authenticated{r, None{}}])), R.render_error(S.Authentication{}, s, False{}, delivery)),
        R.render_branch(m, s, R.AutRefusal{r, delivery}), R.AutRefusal{r, delivery},
        Adm.two_associations(R.render_received(m, r), R.micro_authentication(m), Q.Authenticated{r, None{}}, R.render_error(S.Authentication{}, s, False{}, delivery)),
        prefix(Q.concatenate(R.render_received(m, r), Q.concatenate(R.micro_authentication(m), [Q.Authenticated{r, None{}}])), R.render_error(S.Authentication{}, s, False{}, delivery), R.AutRefusal{r, delivery}, auth_none_without_close(m, r), causes_error(S.Authentication{}, s, False{}, delivery, R.AutRefusal{r, delivery})))
    case R.GateRefusal{+r, +ctx, +delivery}:
      swap_causes(Q.concatenate(Q.concatenate(R.render_authenticated(m, r, ctx), [Q.Rejected{r, ctx}]), R.render_error(S.Certificate{}, s, False{}, delivery)),
        R.render_branch(m, s, R.GateRefusal{r, ctx, delivery}), R.GateRefusal{r, ctx, delivery},
        Q.concatenate_assoc(R.render_authenticated(m, r, ctx), [Q.Rejected{r, ctx}], R.render_error(S.Certificate{}, s, False{}, delivery)),
        prefix(Q.concatenate(R.render_authenticated(m, r, ctx), [Q.Rejected{r, ctx}]), R.render_error(S.Certificate{}, s, False{}, delivery), R.GateRefusal{r, ctx, delivery},
          concatenate(R.render_authenticated(m, r, ctx), [Q.Rejected{r, ctx}], authenticated(m, r, ctx), front(Q.Rejected{r, ctx}, Nil{}, {==}, empty())), causes_error(S.Certificate{}, s, False{}, delivery, R.GateRefusal{r, ctx, delivery})))
    case R.Executed{+r, +ctx, +xs, +p, +delivery}: prefix(R.render_execution(m, r, ctx, xs), Q.concatenate(R.micro_output(m), R.render_final(p, s, False{}, delivery)), R.Executed{r, ctx, xs, p, delivery}, execution(m, r, ctx, xs),
      prefix(R.micro_output(m), R.render_final(p, s, False{}, delivery), R.Executed{r, ctx, xs, p, delivery}, micro_output(m), causes_conclusion(N.conclude(p, s), False{}, delivery, R.Executed{r, ctx, xs, p, delivery})))
    case R.FailureBefore{+f, +stage, +id, +fatal, +delivery}: prefix(R.render_phase(m, f), R.render_failure(s, stage, id, fatal, delivery), R.FailureBefore{f, stage, id, fatal, delivery}, phase(m, f), causes_failure(s, stage, id, fatal, delivery, R.FailureBefore{f, stage, id, fatal, delivery}))
    case R.FatalAfterPublication{+r, +ctx, +xs, +p, +stage, +id}: prefix(R.render_execution(m, r, ctx, xs), Q.concatenate(R.micro_output(m), R.render_fatal_published(N.conclude(p, s), stage, id)), R.FatalAfterPublication{r, ctx, xs, p, stage, id}, execution(m, r, ctx, xs),
      prefix(R.micro_output(m), R.render_fatal_published(N.conclude(p, s), stage, id), R.FatalAfterPublication{r, ctx, xs, p, stage, id}, micro_output(m), causes_fatal_published(N.conclude(p, s), stage, id, R.FatalAfterPublication{r, ctx, xs, p, stage, id})))
    case R.Pending{+f}: without_closure(R.render_phase(m, f), R.Pending{f}, phase(m, f))
    case R.InitialPending{+accepts}: without_closure(R.prefix_initial(m, accepts), R.InitialPending{accepts}, prefix_initial_without_close(m, accepts))

def causes_of_branch(+m: R.Micro, +s: D.State, +branch: R.Branch) -> Causes(R.render(m, s, branch), branch):
  prefix([Q.Configured{}], R.render_branch(m, s, branch), branch, front(Q.Configured{}, Nil{}, {==}, empty()), causes_without_config(m, s, branch))

# Replace only the WithoutResponse branch by inversion of the actual selector.
def CauseSemantics(~c: S.Configuration, -world: Nat, -s: D.State, -reception: X.Reception,
  -xs: List<&2, Q.Frame>, -t: Nat) -> Type:
  L.Disjunction<K.WithoutResponseExpected(I.Serve{world, c, s, reception}),
    L.Disjunction<&stage: X.Stage -> &id: String -> Adm.Before(xs, t, Q.Failed{stage, id, True{}}),
      L.Disjunction<&r: S.Response -> &w: D.State -> Adm.Before(xs, t, Q.Completed{r, w, True{}}),
        &bs: List<&2, U32> -> Adm.Before(xs, t, Q.Interrupted{bs})>>>

def apply_semantics(~c: S.Configuration, -world: Nat, -s: D.State, -reception: X.Reception,
  -xs: List<&2, Q.Frame>, -t: Nat, -branch: R.Branch,
  selector: {branch == R.WithoutResponse{} : R.Branch} -> K.WithoutResponseExpected(I.Serve{world, c, s, reception}),
  cause: Cause(xs, t, branch)) -> CauseSemantics(c, world, s, reception, xs, t):
  match cause:
    case L.Left{without}: L.Left{selector(without)}
    case L.Right{rest}: L.Right{rest}

def before_in_service(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +reception: X.Reception,
  -t: Nat, +q: Q.Frame, f: I.Fact, relation: Q.rel_fact(c, Five.program_of_world(source, world), q, f), milestone: Linkage.Milestone(f),
  canonical: {I.Serve{world, c, s, reception} == Source.scenario(source, world) : I.Scenario},
  before: Adm.Before(Vis.frames_call(c, s, reception, Source.call(source, world)), t, q)) ->
  I.Before(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t, f):
  match before:
    case (+u, L.Both{order, query_result}): (u, L.Both{order,
      Linkage.introduce_frame(source, c, world, s, reception, u, q, f, canonical, query_result, relation, milestone)})

def close_of_cause(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +reception: X.Reception, +t: Nat,
  canonical: {I.Serve{world, c, s, reception} == Source.scenario(source, world) : I.Scenario},
  cause: CauseSemantics(c, world, s, reception, Vis.frames_call(c, s, reception, Source.call(source, world)), t)) ->
  K.Rule7(I.ClosedChannel{}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t):
  match cause:
    case L.Left{without}: L.Left{without}
    case L.Right{L.Left{(+stage, +id, before)}}:
      L.Right{L.Left{(stage, id, before_in_service(source, c, world, s, reception, t, Q.Failed{stage, id, True{}}, I.FailedEnvironment{stage, id, True{}}, {==}, Unit{}, canonical, before))}}
    case L.Right{L.Right{L.Left{(+r, +w, before)}}}:
      L.Right{L.Right{L.Left{(r, w, before_in_service(source, c, world, s, reception, t, Q.Completed{r, w, True{}}, I.Concluded{r, w, True{}}, {==}, Unit{}, canonical, before))}}}
    case L.Right{L.Right{L.Right{(+bs, before)}}}:
      L.Right{L.Right{L.Right{(bs, before_in_service(source, c, world, s, reception, t, Q.Interrupted{bs}, I.DeliveryInterrupted{bs}, {==}, Unit{}, canonical, before))}}}

law failure_real_of_call:
  for ~source: Source.Source
  for ~c: S.Configuration
  for +world: Nat
  for +s: D.State
  for +reception: X.Reception
  for +t: Nat
  for +stage: X.Stage
  for +id: String
  for +fatal: Bool
  for real: FailuresReal(source, I.Serve{world, c, s, reception}, Vis.frames_call(c, s, reception, Source.call(source, world)))
  for fact: I.Happens(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t, I.FailedEnvironment{stage, id, fatal})
  K.Rule7(I.FailedEnvironment{stage, id, fatal}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t)
def failure_real_of_call(source, c, world, s, reception, t, stage, id, fatal, real, fact):
  real(t, stage, id, fatal, Linkage.extract_frame(source, c, world, s, reception, t, I.FailedEnvironment{stage, id, fatal}, Unit{}, fact))

# Invert the same pure decision: no technical result manufactures EOF.
def without_response(branch: R.Branch) -> Bool:
  match branch:
    case R.WithoutResponse{}: True{}
    case _: False{}

def cleanup_negative_without(+r: P.Request, +ctx: D.Context, +xs: List<&2, Q.FrameExec>, +p: N.Prepared, cleanup: R.Cleanup, +delivery: R.Delivery) -> {without_response(R.decide_cleanup(r, ctx, xs, p, cleanup, delivery)) == False{} : Bool}:
  match cleanup:
    case R.Clears{}: {==}
    case R.ErrorCleanup{id, fatal}: {==}
    case R.FatalAfterStore{stage, id}: {==}
    case R.PendingCleanup{}: {==}

def execution_negative_without(+r: P.Request, +ctx: D.Context, output: R.OutputExecution, +cleanup: R.Cleanup, +delivery: R.Delivery) -> {without_response(R.decide_execution(r, ctx, output, cleanup, delivery)) == False{} : Bool}:
  match output:
    case R.Finalized{+xs, +p}: cleanup_negative_without(r, ctx, xs, p, cleanup, delivery)
    case R.ErrorExecution{point, stage, id, fatal}: {==}
    case R.PendingExecution{point}: {==}

def judgment_negative_without(+r: P.Request, +ctx: D.Context, data: R.DataTools) -> {without_response(R.decide_judgment(r, ctx, data)) == False{} : Bool}:
  match data:
    case R.DataTools{j, +ex, +li, +en, pre}:
      match j:
        case R.Accepted{}: execution_negative_without(r, ctx, ex, li, en)
        case R.Refused{}: {==}
        case R.ErrorJudgment{id, fatal}: {==}
        case R.PendingJudgment{}: {==}

def identity_negative_without(ctx: Maybe<&2, D.Context>, +r: P.Request, +data: R.DataTools) -> {without_response(R.decide_identity(ctx, r, data)) == False{} : Bool}:
  match ctx:
    case None{}:
      match data:
        case R.DataTools{j, ex, li, en, pre}: {==}
    case Some{+c}: judgment_negative_without(r, c, data)

def auth_negative_without(pre: R.Preprocessing, +state: D.State, +r: P.Request, +data: R.DataTools) -> {without_response(R.decide_authentication(pre, state, r, data)) == False{} : Bool}:
  match pre:
    case R.Normal{}: identity_negative_without(D.authenticate(state, I.credential(r)), r, data)
    case R.FailureFraming{id, fatal}: identity_negative_without(D.authenticate(state, I.credential(r)), r, data)
    case R.FailureDecode{id, fatal}: identity_negative_without(D.authenticate(state, I.credential(r)), r, data)
    case R.FailureAuth{id, fatal}: {==}
    case R.PendingFraming{}: identity_negative_without(D.authenticate(state, I.credential(r)), r, data)
    case R.PendingDecode{}: identity_negative_without(D.authenticate(state, I.credential(r)), r, data)
    case R.PendingAuth{}: {==}

def pre_negative_without(input: Input.PreAuthentication, +data: R.DataTools) -> {without_response(R.decide_pre(input, data)) == False{} : Bool}:
  match input:
    case Input.InputReady{+s, +r}: auth_negative_without(R.preprocessing(data), s, r, data)
    case Input.ErrorMessage{status}:
      match data:
        case R.DataTools{j, ex, li, en, pre}: {==}
    case Input.ErrorTransport{}:
      match data:
        case R.DataTools{j, ex, li, en, pre}: {==}

def decode_negative_without(pre: R.Preprocessing, +bytes: List<&2, U32>, +e: D.Schema, +lim: S.Limits, +data: R.DataTools) -> {without_response(R.decide_decode(pre, bytes, e, lim, data)) == False{} : Bool}:
  match pre:
    case R.Normal{}: pre_negative_without(Input.decode(bytes, e, lim), data)
    case R.FailureFraming{id, fatal}: pre_negative_without(Input.decode(bytes, e, lim), data)
    case R.FailureDecode{id, fatal}: {==}
    case R.FailureAuth{id, fatal}: pre_negative_without(Input.decode(bytes, e, lim), data)
    case R.PendingFraming{}: pre_negative_without(Input.decode(bytes, e, lim), data)
    case R.PendingDecode{}: {==}
    case R.PendingAuth{}: pre_negative_without(Input.decode(bytes, e, lim), data)

def packet_negative_without(packet: Maybe<&2, List<&2, U32>>, +e: D.Schema, +lim: S.Limits, +data: R.DataTools) -> {without_response(R.decide_packet(packet, e, lim, data)) == False{} : Bool}:
  match packet:
    case None{}:
      match data:
        case R.DataTools{j, ex, li, en, pre}: {==}
    case Some{+bs}: decode_negative_without(R.preprocessing(data), bs, e, lim, data)

def dispo_without_response(d: X.Disposition, +state: List<&2, U32>, +e: D.Schema, +lim: S.Limits, +data: R.DataTools,
  mark: {without_response(R.decide_disposition(d, state, e, lim, data)) == True{} : Bool}) -> {d == X.CloseWithoutResponse{} : X.Disposition}:
  match d:
    case X.CloseWithoutResponse{}: {==}
    case X.RefuseClose{+status}:
      match data:
        case R.DataTools{j, ex, li, en, pre}: F.absurd_boolean({X.RefuseClose{status} == X.CloseWithoutResponse{} : X.Disposition}, mark)
    case X.RefuseContinue{+status}:
      match data:
        case R.DataTools{j, ex, li, en, pre}: F.absurd_boolean({X.RefuseContinue{status} == X.CloseWithoutResponse{} : X.Disposition}, mark)
    case X.ProcessBody{+body}:
      L.ex_false({X.ProcessBody{body} == X.CloseWithoutResponse{} : X.Disposition},
        F.false_negative_true(Equal.trans(Bool, False{}, without_response(R.decide_packet(Transport.join(state, body), e, lim, data)), True{},
          Equal.sym(Bool, without_response(R.decide_packet(Transport.join(state, body), e, lim, data)), False{}, packet_negative_without(Transport.join(state, body), e, lim, data)), mark)))

def enq_without_response(pre: R.Preprocessing, +d: X.Disposition, +state: List<&2, U32>, +e: D.Schema, +lim: S.Limits, +data: R.DataTools,
  mark: {without_response(R.decide_framing(pre, d, state, e, lim, data)) == True{} : Bool}) -> {d == X.CloseWithoutResponse{} : X.Disposition}:
  match pre:
    case R.Normal{}: dispo_without_response(d, state, e, lim, data, mark)
    case R.FailureFraming{id, fatal}: F.absurd_boolean({d == X.CloseWithoutResponse{} : X.Disposition}, mark)
    case R.FailureDecode{id, fatal}: dispo_without_response(d, state, e, lim, data, mark)
    case R.FailureAuth{id, fatal}: dispo_without_response(d, state, e, lim, data, mark)
    case R.PendingFraming{}: F.absurd_boolean({d == X.CloseWithoutResponse{} : X.Disposition}, mark)
    case R.PendingDecode{}: dispo_without_response(d, state, e, lim, data, mark)
    case R.PendingAuth{}: dispo_without_response(d, state, e, lim, data, mark)

# Uses neither Processable nor tool success: it only inverts R.decide.
law without_response_requires_end_of_input:
  for ~c: S.Configuration
  for +reception: X.Reception
  for +state: List<&2, U32>
  for +data: R.DataTools
  for same: {R.decide(c, reception, state, data) == R.WithoutResponse{} : R.Branch}
  {X.decide_reception(c, reception) == X.CloseWithoutResponse{} : X.Disposition}
def without_response_requires_end_of_input(c, reception, state, data, same):
  enq_without_response(R.preprocessing(data), X.decide_reception_in(S.limits(c), reception), state, S.schema(c), S.limits(c), data,
    Equal.trans(Bool, without_response(R.decide_framing(R.preprocessing(data), X.decide_reception_in(S.limits(c), reception), state, S.schema(c), S.limits(c), data)),
      without_response(R.decide(c, reception, state, data)), True{},
      Equal.cong(R.Branch, Bool, without_response, R.decide_framing(R.preprocessing(data), X.decide_reception_in(S.limits(c), reception), state, S.schema(c), S.limits(c), data), R.decide(c, reception, state, data),
        Equal.sym(R.Branch, R.decide(c, reception, state, data), R.decide_framing(R.preprocessing(data), X.decide_reception_in(S.limits(c), reception), state, S.schema(c), S.limits(c), data), Five.decide_by_projections(c, reception, state, data))),
      Equal.cong(R.Branch, Bool, without_response, R.decide(c, reception, state, data), R.WithoutResponse{}, same)))

def CausesOfCall(~c: S.Configuration, -world: Nat, +s: D.State, +reception: X.Reception, +data: Source.CallData) -> Type:
  @t: Nat -> {Q.query(Vis.frames_call(c, s, reception, data), t) == Some{Q.Closed{}} : Maybe<&2, Q.Frame>} ->
    CauseSemantics(c, world, s, reception, Vis.frames_call(c, s, reception, data), t)

def causes_semantics_of_call(~c: S.Configuration, +world: Nat, +s: D.State, +reception: X.Reception, data: Source.CallData) -> CausesOfCall(c, world, s, reception, data):
  match data:
    case Source.CallData{cf, ps, pf, tf, +state, +tools, +micro}:
      +t => query_result => apply_semantics(c, world, s, reception, R.generate(c, reception, state, s, tools, micro), t, R.decide(c, reception, state, tools),
        same => without_response_requires_end_of_input(c, reception, state, tools, same),
        causes_of_branch(micro, s, R.decide(c, reception, state, tools))(t, query_result))

law closure_real_of_call:
  for ~source: Source.Source
  for ~c: S.Configuration
  for +world: Nat
  for +s: D.State
  for +reception: X.Reception
  for +t: Nat
  for canonical: {I.Serve{world, c, s, reception} == Source.scenario(source, world) : I.Scenario}
  for fact: I.Happens(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t, I.ClosedChannel{})
  K.Rule7(I.ClosedChannel{}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t)
def closure_real_of_call(source, c, world, s, reception, t, canonical, fact):
  close_of_cause(source, c, world, s, reception, t, canonical,
    causes_semantics_of_call(c, world, s, reception, Source.call(source, world))(t,
      Linkage.extract_frame(source, c, world, s, reception, t, I.ClosedChannel{}, Unit{}, fact)))

# Initialization has only its own facts, including worker failure.
def extract_initial_data(~source: Source.Source, ~c: S.Configuration, +s: D.State, data: Source.InitialData, +t: Nat, f: I.Fact,
  milestone: Linkage.Milestone(f), obs: Source.of_observation(source, c, Source.construct_initial(Source.identity(source), c, s, data), t, f)) ->
  {Q.query(Vis.frames_initial(source, c, s, data), t) == Some{Q.frame_of_fact(f)} : Maybe<&2, Q.Frame>}:
  match data:
    case Source.InitialData{cf, sf, pf, +j, +result, +micro}:
      Q.observation_frame(c, Source.without_program(), R.generate_result_initial(c, Source.identity(source), s, j, result, micro), t, f,
        Linkage.select_milestone(c, Source.without_program(), None{}, R.generate_result_initial(c, Source.identity(source), s, j, result, micro), t, f, milestone, obs))

def extract_initial(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +pi: String, +t: Nat, f: I.Fact,
  milestone: Linkage.Milestone(f), literal: L.E<{Source.artifact(source) == Source.artifact(source) : String}, L.E<{I.Initialize{world, c, s, pi} == Source.scenario(source, world) : I.Scenario},
    Source.of_route(source, I.Initialize{world, c, s, pi}, t, f)>>) ->
  {Q.query(Vis.frames_initial(source, c, s, Source.initial(source, world)), t) == Some{Q.frame_of_fact(f)} : Maybe<&2, Q.Frame>}:
  match literal:
    case L.Both{name, L.Both{canonical, obs}}: extract_initial_data(source, c, s, Source.initial(source, world), t, f, milestone, obs)

law failure_real_of_initialization:
  for ~source: Source.Source
  for ~c: S.Configuration
  for +world: Nat
  for +s: D.State
  for +pi: String
  for +t: Nat
  for +stage: X.Stage
  for +id: String
  for +fatal: Bool
  for real: FailuresReal(source, I.Initialize{world, c, s, pi}, Vis.frames_initial(source, c, s, Source.initial(source, world)))
  for fact: I.Happens(Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t, I.FailedEnvironment{stage, id, fatal})
  K.Rule7(I.FailedEnvironment{stage, id, fatal}, Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t)
def failure_real_of_initialization(source, c, world, s, pi, t, stage, id, fatal, real, fact):
  real(t, stage, id, fatal, extract_initial(source, c, world, s, pi, t, I.FailedEnvironment{stage, id, fatal}, Unit{},
    Source.eliminate_fact_literal(source, Source.artifact(source), I.Initialize{world, c, s, pi}, t, I.FailedEnvironment{stage, id, fatal}, fact)))

def initial_negative_closes(+m: R.Micro, +s: D.State, j: R.Judgment, result: R.ResultInitial, +is_valid: Bool) -> NotClose(R.render(m, s, R.decide_judgment_initial(j, result, is_valid))):
  match j:
    case R.Accepted{}:
      match result:
        case R.InitializationFinished{}:
          match is_valid:
            case False{}: front(Q.Configured{}, [Q.InitialRefused{S.DataError{}}], {==}, front(Q.InitialRefused{S.DataError{}}, Nil{}, {==}, empty()))
            case True{}: front(Q.Configured{}, R.render_branch(m, s, R.InitialOk{}), {==},
              front(Q.InitialAccepts{}, Q.concatenate(R.micro_output(m), R.render_initial(P.encode(D.state_value(s)), s)), {==}, concatenate(R.micro_output(m), R.render_initial(P.encode(D.state_value(s)), s), micro_output(m), initial_without_close(P.encode(D.state_value(s)), s))))
        case R.FailedInitial{+accepts, +stage, +id, +fatal}:
          front(Q.Configured{}, R.render_branch(m, s, R.InitialFailure{accepts && is_valid, stage, id, fatal}), {==},
            concatenate(R.prefix_initial(m, accepts && is_valid), [Q.Failed{stage, id, fatal}, Q.InitialRefused{S.Failure{}}], prefix_initial_without_close(m, accepts && is_valid),
              front(Q.Failed{stage, id, fatal}, [Q.InitialRefused{S.Failure{}}], {==}, front(Q.InitialRefused{S.Failure{}}, Nil{}, {==}, empty()))))
        case R.PendingInitial{+accepts}: front(Q.Configured{}, R.prefix_initial(m, accepts && is_valid), {==}, prefix_initial_without_close(m, accepts && is_valid))
    case R.Refused{}: front(Q.Configured{}, [Q.InitialRefused{S.Certificate{}}], {==}, front(Q.InitialRefused{S.Certificate{}}, Nil{}, {==}, empty()))
    case R.ErrorJudgment{+id, +fatal}: front(Q.Configured{}, [Q.Failed{X.Verify{}, id, fatal}, Q.InitialRefused{S.Failure{}}], {==},
      front(Q.Failed{X.Verify{}, id, fatal}, [Q.InitialRefused{S.Failure{}}], {==}, front(Q.InitialRefused{S.Failure{}}, Nil{}, {==}, empty())))
    case R.PendingJudgment{}: front(Q.Configured{}, Nil{}, {==}, empty())

def data_initial_negative_close(~source: Source.Source, ~c: S.Configuration, +s: D.State, data: Source.InitialData) -> NotClose(Vis.frames_initial(source, c, s, data)):
  match data:
    case Source.InitialData{cf, sf, pf, +j, +result, +micro}: initial_negative_closes(micro, s, j, result, Config.is_valid(c, Source.identity(source)))

law closure_of_initialization_impossible:
  for ~source: Source.Source
  for ~c: S.Configuration
  for +world: Nat
  for +s: D.State
  for +pi: String
  for +t: Nat
  for fact: I.Happens(Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t, I.ClosedChannel{})
  Empty
def closure_of_initialization_impossible(source, c, world, s, pi, t, fact):
  data_initial_negative_close(source, c, s, Source.initial(source, world))(t,
    extract_initial(source, c, world, s, pi, t, I.ClosedChannel{}, Unit{}, Source.eliminate_fact_literal(source, Source.artifact(source), I.Initialize{world, c, s, pi}, t, I.ClosedChannel{}, fact)))
