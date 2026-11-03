# Authentication/admission of the same generated protocol. Denotations are
# the checked closed declarations; fact order is proved here.
import Base
import ../contract/Data.bend as D
import ../contract/Interface.bend as I
import ../contract/LAWS.bend as K
import ../contract/Logic.bend as L
import ../contract/Protocol.bend as P
import ../contract/Semantics.bend as S
import ../contract/Resources.bend as X
import ../src/Core.bend as N
import ./SourceService.bend as Source
import ./RoutesService.bend as R
import ./ProtocolService.bend as Q
import ./PrimitivesService.bend as M
import ./Law5Service.bend as Five
import ./Foundations.bend as F
import ../src/ConfigurationCheck.bend as Config
import ./ScenariosService.bend as Scenarios
import ./HistoryService.bend as History
import ./ModelService.bend as Model
import ./CodecSums.bend as A

# Content separate from chronology: not a supplied Rule3/4.
def Content(~source: Source.Source, -c: S.Configuration, -s: D.State,
  +origin: Source.JudgmentSyntactic, q: Q.Frame) -> Type:
  match q:
    case Q.Authenticated{r, ctx}: {ctx == D.authenticate(s, I.credential(r)) : Maybe<&2, D.Context>}
    case Q.Accepts{r, ctx}: I.CertificateValid(Source.environment(source), c, r, ctx, Source.program(source, origin))
    case Q.Rejected{r, ctx}: I.WithoutCertificate(Source.environment(source), c, r, ctx)
    case Q.Started{r, ctx}: {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>}
    case _: Unit

def Before(-xs: List<&2, Q.Frame>, -t: Nat, -q: Q.Frame) -> Type:
  &u: Nat -> L.E<{Nat.is_lt(u, t) == True{} : Bool}, {Q.query(xs, u) == Some{q} : Maybe<&2, Q.Frame>}>

def Order(-xs: List<&2, Q.Frame>, -t: Nat, q: Q.Frame) -> Type:
  match q:
    case Q.Authenticated{r, ctx}: Before(xs, t, Q.Received{r})
    case Q.Accepts{r, ctx}: Before(xs, t, Q.Authenticated{r, Some{ctx}})
    case Q.Rejected{r, ctx}: Before(xs, t, Q.Authenticated{r, Some{ctx}})
    case Q.Started{r, ctx}: L.E<Before(xs, t, Q.Authenticated{r, Some{ctx}}), Before(xs, t, Q.Accepts{r, ctx})>
    case _: Unit

def FrameFacts(~source: Source.Source, -c: S.Configuration, -s: D.State,
  +origin: Source.JudgmentSyntactic, -xs: List<&2, Q.Frame>, -t: Nat, +q: Q.Frame) -> Type:
  L.E<Content(source, c, s, origin, q), Order(xs, t, q)>

def Validation(~source: Source.Source, -c: S.Configuration, -s: D.State,
  +origin: Source.JudgmentSyntactic, +xs: List<&2, Q.Frame>) -> Type:
  @t: Nat -> @q: Q.Frame -> {Q.query(xs, t) == Some{q} : Maybe<&2, Q.Frame>} -> FrameFacts(source, c, s, origin, xs, t, q)

def neutral(q: Q.Frame) -> Bool:
  match q:
    case Q.Authenticated{r, ctx}: False{}
    case Q.Accepts{r, ctx}: False{}
    case Q.Rejected{r, ctx}: False{}
    case Q.Started{r, ctx}: False{}
    case _: True{}

def Neutral(xs: List<&2, Q.Frame>) -> Type:
  match xs:
    case Nil{}: Unit
    case Con{h, t}: L.E<{neutral(h) == True{} : Bool}, Neutral(t)>

def neutral_concatenated(+xs: List<&2, Q.Frame>, -ys: List<&2, Q.Frame>, a: Neutral(xs), b: Neutral(ys)) -> Neutral(Q.concatenate(xs, ys)):
  match xs a:
    case Nil{} _: b
    case Con{h, t} L.Both{head, tail}: L.Both{head, neutral_concatenated(t, ys, tail, b)}

def query_prefix(+xs: List<&2, Q.Frame>, -ys: List<&2, Q.Frame>, +t: Nat, -q: Q.Frame,
  present: {Q.query(xs, t) == Some{q} : Maybe<&2, Q.Frame>}) -> {Q.query(Q.concatenate(xs, ys), t) == Some{q} : Maybe<&2, Q.Frame>}:
  Q.query_prefix(xs, ys, t, q, present)

def before_prefix(+xs: List<&2, Q.Frame>, -ys: List<&2, Q.Frame>, -t: Nat, -q: Q.Frame, before: Before(xs, t, q)) -> Before(Q.concatenate(xs, ys), t, q):
  match before:
    case (+u, L.Both{order, query_result}): (u, L.Both{order, query_prefix(xs, ys, u, q, query_result)})

def order_prefix(+xs: List<&2, Q.Frame>, -ys: List<&2, Q.Frame>, -t: Nat, q: Q.Frame, order: Order(xs, t, q)) -> Order(Q.concatenate(xs, ys), t, q):
  match q:
    case Q.Authenticated{r, ctx}: before_prefix(xs, ys, t, Q.Received{r}, order)
    case Q.Accepts{r, ctx}: before_prefix(xs, ys, t, Q.Authenticated{r, Some{ctx}}, order)
    case Q.Rejected{r, ctx}: before_prefix(xs, ys, t, Q.Authenticated{r, Some{ctx}}, order)
    case Q.Started{r, ctx}:
      match order:
        case L.Both{aut, cert}: L.Both{before_prefix(xs, ys, t, Q.Authenticated{r, Some{ctx}}, aut), before_prefix(xs, ys, t, Q.Accepts{r, ctx}, cert)}
    case Q.Configured{}: Unit{}
    case Q.InitialAccepts{}: Unit{}
    case Q.Initialized{a0}: Unit{}
    case Q.InitialRefused{a0}: Unit{}
    case Q.Encoded{a0, a1}: Unit{}
    case Q.Decoded{a0, a1}: Unit{}
    case Q.Stored{a0, a1, a2}: Unit{}
    case Q.Checked{a0, a1}: Unit{}
    case Q.Constructed{a0, a1}: Unit{}
    case Q.Read{a0, a1, a2}: Unit{}
    case Q.Received{a0}: Unit{}
    case Q.Evaluated{a0, a1, a2}: Unit{}
    case Q.Operated{a0, a1, a2, a3}: Unit{}
    case Q.Prepared{a0, a1}: Unit{}
    case Q.Published{a0}: Unit{}
    case Q.Visible{a0}: Unit{}
    case Q.Failed{a0, a1, a2}: Unit{}
    case Q.Completed{a0, a1, a2}: Unit{}
    case Q.Delivered{a0}: Unit{}
    case Q.Interrupted{a0}: Unit{}
    case Q.Closed{}: Unit{}
    case Q.Next{a0, a1}: Unit{}
    case Q.Inspection{a0}: Unit{}
    case Q.Effect{a0}: Unit{}

def data_prefix(~source: Source.Source, -c: S.Configuration, -s: D.State, +origin: Source.JudgmentSyntactic,
  +xs: List<&2, Q.Frame>, -ys: List<&2, Q.Frame>, -t: Nat, +q: Q.Frame, data: FrameFacts(source, c, s, origin, xs, t, q)) -> FrameFacts(source, c, s, origin, Q.concatenate(xs, ys), t, q):
  match data:
    case L.Both{content, order}: L.Both{content, order_prefix(xs, ys, t, q, order)}

# The neutral list proves absence of four milestones, without a second parser.
def neutral_queried(xs: List<&2, Q.Frame>, t: Nat, +q: Q.Frame, proofs: Neutral(xs),
  query_result: {Q.query(xs, t) == Some{q} : Maybe<&2, Q.Frame>}) -> {neutral(q) == True{} : Bool}:
  match xs t:
    case Nil{} _: L.ex_false({neutral(q) == True{} : Bool}, F.none_negative_some(Q.Frame, q, query_result))
    case Con{+h, tail} 0n:
      F.combined_pair({neutral(q) == True{} : Bool}, {neutral(h) == True{} : Bool}, Neutral(tail), proofs, head => rest =>
        %F.some_injective(Q.Frame, h, q, query_result) : {neutral(_) == True{} : Bool} head)
    case Con{h, tail} 1n+k:
      F.combined_pair({neutral(q) == True{} : Bool}, {neutral(h) == True{} : Bool}, Neutral(tail), proofs, head => rest => neutral_queried(tail, k, q, rest, query_result))

def data_neutral(~source: Source.Source, -c: S.Configuration, -s: D.State, +origin: Source.JudgmentSyntactic,
  -xs: List<&2, Q.Frame>, -t: Nat, q: Q.Frame, h: {neutral(q) == True{} : Bool}) -> FrameFacts(source, c, s, origin, xs, t, q):
  match q:
    case Q.Configured{}: L.Both{Unit{}, Unit{}}
    case Q.InitialAccepts{}: L.Both{Unit{}, Unit{}}
    case Q.Initialized{a0}: L.Both{Unit{}, Unit{}}
    case Q.InitialRefused{a0}: L.Both{Unit{}, Unit{}}
    case Q.Encoded{a0, a1}: L.Both{Unit{}, Unit{}}
    case Q.Decoded{a0, a1}: L.Both{Unit{}, Unit{}}
    case Q.Stored{a0, a1, a2}: L.Both{Unit{}, Unit{}}
    case Q.Checked{a0, a1}: L.Both{Unit{}, Unit{}}
    case Q.Constructed{a0, a1}: L.Both{Unit{}, Unit{}}
    case Q.Read{a0, a1, a2}: L.Both{Unit{}, Unit{}}
    case Q.Received{a0}: L.Both{Unit{}, Unit{}}
    case Q.Authenticated{a0, a1}: F.absurd_boolean(FrameFacts(source, c, s, origin, xs, t, Q.Authenticated{a0, a1}), h)
    case Q.Accepts{a0, a1}: F.absurd_boolean(FrameFacts(source, c, s, origin, xs, t, Q.Accepts{a0, a1}), h)
    case Q.Rejected{a0, a1}: F.absurd_boolean(FrameFacts(source, c, s, origin, xs, t, Q.Rejected{a0, a1}), h)
    case Q.Started{a0, a1}: F.absurd_boolean(FrameFacts(source, c, s, origin, xs, t, Q.Started{a0, a1}), h)
    case Q.Evaluated{a0, a1, a2}: L.Both{Unit{}, Unit{}}
    case Q.Operated{a0, a1, a2, a3}: L.Both{Unit{}, Unit{}}
    case Q.Prepared{a0, a1}: L.Both{Unit{}, Unit{}}
    case Q.Published{a0}: L.Both{Unit{}, Unit{}}
    case Q.Visible{a0}: L.Both{Unit{}, Unit{}}
    case Q.Failed{a0, a1, a2}: L.Both{Unit{}, Unit{}}
    case Q.Completed{a0, a1, a2}: L.Both{Unit{}, Unit{}}
    case Q.Delivered{a0}: L.Both{Unit{}, Unit{}}
    case Q.Interrupted{a0}: L.Both{Unit{}, Unit{}}
    case Q.Closed{}: L.Both{Unit{}, Unit{}}
    case Q.Next{a0, a1}: L.Both{Unit{}, Unit{}}
    case Q.Inspection{a0}: L.Both{Unit{}, Unit{}}
    case Q.Effect{a0}: L.Both{Unit{}, Unit{}}

def validate_neutral(~source: Source.Source, -c: S.Configuration, -s: D.State, +origin: Source.JudgmentSyntactic,
  +xs: List<&2, Q.Frame>, h: Neutral(xs)) -> Validation(source, c, s, origin, xs):
  +t => +q => query_result => data_neutral(source, c, s, origin, xs, t, q, neutral_queried(xs, t, q, h, query_result))

def branch_concat_neutral(~source: Source.Source, -c: S.Configuration, -s: D.State, +origin: Source.JudgmentSyntactic,
  +xs: List<&2, Q.Frame>, +ys: List<&2, Q.Frame>, +t: Nat, +q: Q.Frame,
  a: Validation(source, c, s, origin, xs), b: Neutral(ys), part: Q.Part(xs, ys, t, q)) -> FrameFacts(source, c, s, origin, Q.concatenate(xs, ys), t, q):
  match part:
    case L.Left{(+u, L.Both{position, query_result})}:
      %Equal.sym(Nat, t, u, position) : FrameFacts(source, c, s, origin, Q.concatenate(xs, ys), _, q)
      data_prefix(source, c, s, origin, xs, ys, u, q, a(u, q, query_result))
    case L.Right{(+u, L.Both{position, query_result})}:
      data_neutral(source, c, s, origin, Q.concatenate(xs, ys), t, q, neutral_queried(ys, u, q, b, query_result))

def attach_neutral(~source: Source.Source, -c: S.Configuration, -s: D.State, +origin: Source.JudgmentSyntactic,
  +xs: List<&2, Q.Frame>, +ys: List<&2, Q.Frame>, a: Validation(source, c, s, origin, xs), b: Neutral(ys)) -> Validation(source, c, s, origin, Q.concatenate(xs, ys)):
  +t => +q => query_result => branch_concat_neutral(source, c, s, origin, xs, ys, t, q, a, b, Q.divide_query(xs, ys, t, q, query_result))

def mark_of_part(~source: Source.Source, -c: S.Configuration, -s: D.State, +origin: Source.JudgmentSyntactic,
  +xs: List<&2, Q.Frame>, +mark: Q.Frame, -t: Nat, +q: Q.Frame, u: Nat,
  datum: FrameFacts(source, c, s, origin, Q.concatenate(xs, [mark]), Nat.add(Q.size(xs), 0n), mark),
  position: {t == Nat.add(Q.size(xs), u) : Nat}, query_result: {Q.query([mark], u) == Some{q} : Maybe<&2, Q.Frame>}) -> FrameFacts(source, c, s, origin, Q.concatenate(xs, [mark]), t, q):
  match u:
    case 0n:
      %Equal.sym(Nat, t, Nat.add(Q.size(xs), 0n), position) : FrameFacts(source, c, s, origin, Q.concatenate(xs, [mark]), _, q)
      %F.some_injective(Q.Frame, mark, q, query_result) : FrameFacts(source, c, s, origin, Q.concatenate(xs, [mark]), Nat.add(Q.size(xs), 0n), _)
      datum
    case 1n+k:
      L.ex_false(FrameFacts(source, c, s, origin, Q.concatenate(xs, [mark]), t, q), F.none_negative_some(Q.Frame, q, query_result))

def branch_attach_mark(~source: Source.Source, -c: S.Configuration, -s: D.State, +origin: Source.JudgmentSyntactic,
  +xs: List<&2, Q.Frame>, +mark: Q.Frame, +t: Nat, +q: Q.Frame,
  a: Validation(source, c, s, origin, xs), datum: FrameFacts(source, c, s, origin, Q.concatenate(xs, [mark]), Nat.add(Q.size(xs), 0n), mark),
  part: Q.Part(xs, [mark], t, q)) -> FrameFacts(source, c, s, origin, Q.concatenate(xs, [mark]), t, q):
  match part:
    case L.Left{(+u, L.Both{position, query_result})}:
      %Equal.sym(Nat, t, u, position) : FrameFacts(source, c, s, origin, Q.concatenate(xs, [mark]), _, q)
      data_prefix(source, c, s, origin, xs, [mark], u, q, a(u, q, query_result))
    case L.Right{(u, L.Both{position, query_result})}:
      mark_of_part(source, c, s, origin, xs, mark, t, q, u, datum, position, query_result)

def attach_mark(~source: Source.Source, -c: S.Configuration, -s: D.State, +origin: Source.JudgmentSyntactic,
  +xs: List<&2, Q.Frame>, +mark: Q.Frame, a: Validation(source, c, s, origin, xs),
  datum: FrameFacts(source, c, s, origin, Q.concatenate(xs, [mark]), Nat.add(Q.size(xs), 0n), mark)) -> Validation(source, c, s, origin, Q.concatenate(xs, [mark])):
  +t => +q => query_result => branch_attach_mark(source, c, s, origin, xs, mark, t, q, a, datum, Q.divide_query(xs, [mark], t, q, query_result))

def query_of_mark(+xs: List<&2, Q.Frame>, -q: Q.Frame) ->
  {Q.query(Q.concatenate(xs, [q]), Nat.add(Q.size(xs), 0n)) == Some{q} : Maybe<&2, Q.Frame>}:
  Q.query_after_prefix(xs, [q], 0n)

def before_of_mark(+xs: List<&2, Q.Frame>, -q: Q.Frame, -mark: Q.Frame, +u: Nat,
  query_result: {Q.query(xs, u) == Some{q} : Maybe<&2, Q.Frame>}) -> Before(Q.concatenate(xs, [mark]), Nat.add(Q.size(xs), 0n), q):
  F.combined_pair(Before(Q.concatenate(xs, [mark]), Nat.add(Q.size(xs), 0n), q),
    {Q.query(xs, u) == Some{q} : Maybe<&2, Q.Frame>}, {Q.query(xs, u) == Some{q} : Maybe<&2, Q.Frame>},
    Q.equality_reopenable(Maybe<&2, Q.Frame>, Q.query(xs, u), Some{q}, query_result), one => two =>
      (u, L.Both{(%Equal.sym(Nat, Nat.add(Q.size(xs), 0n), Q.size(xs), A.nat_sum_zero_right(Q.size(xs))) : {Nat.is_lt(u, _) == True{} : Bool}
        Q.position_present_inside(xs, u, q, one)), query_prefix(xs, [mark], u, q, two)}))

def neutral_internal(q: Q.Frame, h: {M.internal(q) == True{} : Bool}) -> {neutral(q) == True{} : Bool}:
  match q:
    case Q.Configured{}: {==}
    case Q.InitialAccepts{}: {==}
    case Q.Initialized{a0}: {==}
    case Q.InitialRefused{a0}: {==}
    case Q.Encoded{a0, a1}: {==}
    case Q.Decoded{a0, a1}: {==}
    case Q.Stored{a0, a1, a2}: {==}
    case Q.Checked{a0, a1}: {==}
    case Q.Constructed{a0, a1}: {==}
    case Q.Read{a0, a1, a2}: {==}
    case Q.Received{a0}: {==}
    case Q.Authenticated{a0, a1}: F.absurd_boolean({neutral(Q.Authenticated{a0, a1}) == True{} : Bool}, h)
    case Q.Accepts{a0, a1}: F.absurd_boolean({neutral(Q.Accepts{a0, a1}) == True{} : Bool}, h)
    case Q.Rejected{a0, a1}: F.absurd_boolean({neutral(Q.Rejected{a0, a1}) == True{} : Bool}, h)
    case Q.Started{a0, a1}: F.absurd_boolean({neutral(Q.Started{a0, a1}) == True{} : Bool}, h)
    case Q.Evaluated{a0, a1, a2}: {==}
    case Q.Operated{a0, a1, a2, a3}: {==}
    case Q.Prepared{a0, a1}: {==}
    case Q.Published{a0}: {==}
    case Q.Visible{a0}: {==}
    case Q.Failed{a0, a1, a2}: {==}
    case Q.Completed{a0, a1, a2}: {==}
    case Q.Delivered{a0}: {==}
    case Q.Interrupted{a0}: {==}
    case Q.Closed{}: {==}
    case Q.Next{a0, a1}: {==}
    case Q.Inspection{a0}: {==}
    case Q.Effect{a0}: {==}

def neutral_internals(xs: List<&2, Q.Frame>, proofs: M.Internal(xs)) -> Neutral(xs):
  match xs proofs:
    case Nil{} _: Unit{}
    case Con{+q, +t} L.Both{head, tail}: L.Both{neutral_internal(q, head), neutral_internals(t, tail)}

def micro_input_neutral(m: R.Micro) -> Neutral(R.micro_input(m)):
  match m:
    case R.Micro{+a, b, c, d}: neutral_internals(M.expand_primitives(a), M.primitives_only_generate_internal(a))
def micro_authentication_neutral(m: R.Micro) -> Neutral(R.micro_authentication(m)):
  match m:
    case R.Micro{a, +b, c, d}: neutral_internals(M.expand_primitives(b), M.primitives_only_generate_internal(b))
def micro_execution_neutral(m: R.Micro) -> Neutral(R.micro_execution(m)):
  match m:
    case R.Micro{a, b, +c, d}: neutral_internals(M.expand_primitives(c), M.primitives_only_generate_internal(c))
def micro_output_neutral(m: R.Micro) -> Neutral(R.micro_output(m)):
  match m:
    case R.Micro{a, b, c, +d}: neutral_internals(M.expand_primitives(d), M.primitives_only_generate_internal(d))

def execution_neutral(+r: P.Request, +ctx: D.Context, xs: List<&2, Q.FrameExec>) -> Neutral(Q.expand_exec(r, ctx, xs)):
  match xs:
    case Nil{}: Unit{}
    case Con{Q.Evaluation{p}, t}: L.Both{{==}, execution_neutral(r, ctx, t)}
    case Con{Q.Operation{e, s, o, r2}, t}: L.Both{{==}, execution_neutral(r, ctx, t)}

def later_delivery_neutral(closes: Bool, -s: D.State, next: Bool) -> Neutral(R.later_delivery(closes, s, next)):
  match closes next:
    case True{} _: L.Both{{==}, Unit{}}
    case False{} True{}: L.Both{{==}, Unit{}}
    case False{} False{}: Unit{}

def delivery_neutral(-s: D.State, -bs: List<&2, U32>, +closes: Bool, delivery: R.Delivery) -> Neutral(R.render_delivery(s, bs, closes, delivery)):
  match delivery:
    case R.Complete{next}: L.Both{{==}, later_delivery_neutral(closes, s, next)}
    case R.Broken{prefix}: L.Both{{==}, L.Both{{==}, Unit{}}}
    case R.PendingDelivery{}: Unit{}

def publication_neutral(r: S.Response, -s: D.State) -> Neutral(R.render_publication(r, s)):
  match r:
    case S.Response{S.Input{}, v}: Unit{}
    case S.Response{S.Authentication{}, v}: Unit{}
    case S.Response{S.Certificate{}, v}: Unit{}
    case S.Response{S.DataError{}, v}: Unit{}
    case S.Response{S.Limit{}, v}: Unit{}
    case S.Response{S.Failure{}, v}: Unit{}
    case S.Response{S.Refusal{}, v}: Unit{}
    case S.Response{S.Success{}, v}: L.Both{{==}, Unit{}}

def conclusion_neutral(conclusion: N.Conclusion, +closes: Bool, delivery: R.Delivery) -> Neutral(R.render_conclusion(conclusion, closes, delivery)):
  match conclusion:
    case N.Conclusion{+s, +r, +bs}: L.Both{{==}, neutral_concatenated(R.render_publication(r, s), Con{Q.Completed{r, s, closes}, R.render_delivery(s, bs, closes, delivery)},
      publication_neutral(r, s), L.Both{{==}, delivery_neutral(s, bs, closes, delivery)})}

def error_framed_neutral(result: Maybe<&2, List<&2, U32>>, -r: S.Response, -s: D.State, +closes: Bool, delivery: R.Delivery) -> Neutral(R.render_error_framed(result, r, s, closes, delivery)):
  match result:
    case None{}: Unit{}
    case Some{+bs}: L.Both{{==}, L.Both{{==}, delivery_neutral(s, bs, closes, delivery)}}

def error_neutral(+status: S.Status, -s: D.State, +closes: Bool, delivery: R.Delivery) -> Neutral(R.render_error(status, s, closes, delivery)):
  error_framed_neutral(P.frame(S.response_value(S.response_error(status))), S.response_error(status), s, closes, delivery)

def failure_end_neutral(+s: D.State, fatal: Bool, delivery: R.Delivery) -> Neutral(R.render_failure_end(s, fatal, delivery)):
  match fatal:
    case True{}: L.Both{{==}, Unit{}}
    case False{}: error_neutral(S.Failure{}, s, False{}, delivery)

def failure_neutral(+s: D.State, -stage: X.Stage, -id: String, +fatal: Bool, delivery: R.Delivery) -> Neutral(R.render_failure(s, stage, id, fatal, delivery)):
  L.Both{{==}, failure_end_neutral(s, fatal, delivery)}

def fatal_neutral(conclusion: N.Conclusion, -stage: X.Stage, -id: String) -> Neutral(R.render_fatal_published(conclusion, stage, id)):
  match conclusion:
    case N.Conclusion{+s, +r, bs}: L.Both{{==}, neutral_concatenated(R.render_publication(r, s), [Q.Failed{stage, id, True{}}, Q.Closed{}], publication_neutral(r, s), L.Both{{==}, L.Both{{==}, Unit{}}})}

def initial_neutral(bs: Maybe<&2, List<&2, U32>>, -s: D.State) -> Neutral(R.render_initial(bs, s)):
  match bs:
    case None{}: L.Both{{==}, Unit{}}
    case Some{bs}: L.Both{{==}, L.Both{{==}, L.Both{{==}, Unit{}}}}

def prefix_initial_neutral(+m: R.Micro, accepts: Bool) -> Neutral(R.prefix_initial(m, accepts)):
  match accepts:
    case False{}: Unit{}
    case True{}: L.Both{{==}, micro_output_neutral(m)}

# Indices below count actual frames, including microframes.
def received(+m: R.Micro, +r: P.Request) -> List<&2, Q.Frame>:
  Con{Q.Configured{}, R.render_received(m, r)}
def before_auth(+m: R.Micro, +r: P.Request) -> List<&2, Q.Frame>:
  Q.concatenate(received(m, r), R.micro_authentication(m))
def authenticated(+m: R.Micro, +r: P.Request, ctx: Maybe<&2, D.Context>) -> List<&2, Q.Frame>:
  Q.concatenate(received(m, r), Q.concatenate(R.micro_authentication(m), [Q.Authenticated{r, ctx}]))
def verified(+m: R.Micro, +r: P.Request, +ctx: D.Context) -> List<&2, Q.Frame>:
  Con{Q.Configured{}, R.render_verified(m, r, ctx)}
def index_received(m: R.Micro) -> Nat:
  Succ{Nat.add(Q.size(R.micro_input(m)), 0n)}
def index_auth(+m: R.Micro, +r: P.Request) -> Nat:
  Nat.add(Q.size(before_auth(m, r)), 0n)
def index_accepts(+m: R.Micro, +r: P.Request, +ctx: D.Context) -> Nat:
  Nat.add(Q.size(authenticated(m, r, Some{ctx})), 0n)

def received_neutral(+m: R.Micro, -r: P.Request) -> Neutral(received(m, r)):
  L.Both{{==}, neutral_concatenated(R.micro_input(m), [Q.Received{r}], micro_input_neutral(m), L.Both{{==}, Unit{}})}

def query_received(+m: R.Micro, -r: P.Request) -> {Q.query(received(m, r), index_received(m)) == Some{Q.Received{r}} : Maybe<&2, Q.Frame>}:
  Q.query_after_prefix(R.micro_input(m), [Q.Received{r}], 0n)

def auth_associative(+m: R.Micro, +r: P.Request, -ctx: Maybe<&2, D.Context>) ->
  {Q.concatenate(before_auth(m, r), [Q.Authenticated{r, ctx}]) == authenticated(m, r, ctx) : List<&2, Q.Frame>}:
  Q.concatenate_assoc(received(m, r), R.micro_authentication(m), [Q.Authenticated{r, ctx}])

def query_auth(+m: R.Micro, +r: P.Request, +ctx: Maybe<&2, D.Context>) ->
  {Q.query(authenticated(m, r, ctx), index_auth(m, r)) == Some{Q.Authenticated{r, ctx}} : Maybe<&2, Q.Frame>}:
  %auth_associative(m, r, ctx) : {Q.query(_, index_auth(m, r)) == Some{Q.Authenticated{r, ctx}} : Maybe<&2, Q.Frame>}
  query_of_mark(before_auth(m, r), Q.Authenticated{r, ctx})

def auth_validated(~source: Source.Source, -c: S.Configuration, -s: D.State, +origin: Source.JudgmentSyntactic,
  +m: R.Micro, +r: P.Request, +ctx: Maybe<&2, D.Context>, exact: {ctx == D.authenticate(s, I.credential(r)) : Maybe<&2, D.Context>}) -> Validation(source, c, s, origin, authenticated(m, r, ctx)):
  %auth_associative(m, r, ctx) : Validation(source, c, s, origin, _)
  attach_mark(source, c, s, origin, before_auth(m, r), Q.Authenticated{r, ctx},
    validate_neutral(source, c, s, origin, before_auth(m, r), neutral_concatenated(received(m, r), R.micro_authentication(m), received_neutral(m, r), micro_authentication_neutral(m))),
    L.Both{exact, before_of_mark(before_auth(m, r), Q.Received{r}, Q.Authenticated{r, ctx}, index_received(m),
      query_prefix(received(m, r), R.micro_authentication(m), index_received(m), Q.Received{r}, query_received(m, r)))})

def accepts_validated(~source: Source.Source, -c: S.Configuration, -s: D.State, +origin: Source.JudgmentSyntactic,
  +m: R.Micro, +r: P.Request, +ctx: D.Context,
  aut: {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>}, judgment: Source.JudgmentAccepted(source, c, r, ctx, origin)) -> Validation(source, c, s, origin, verified(m, r, ctx)):
  attach_mark(source, c, s, origin, authenticated(m, r, Some{ctx}), Q.Accepts{r, ctx},
    auth_validated(source, c, s, origin, m, r, Some{ctx}, Equal.sym(Maybe<&2, D.Context>, D.authenticate(s, I.credential(r)), Some{ctx}, aut)),
    L.Both{Source.certificate_of_judgment(source, c, r, ctx, origin, judgment),
      before_of_mark(authenticated(m, r, Some{ctx}), Q.Authenticated{r, Some{ctx}}, Q.Accepts{r, ctx}, index_auth(m, r), query_auth(m, r, Some{ctx}))})

def rejects_validated(~source: Source.Source, -c: S.Configuration, -s: D.State, +origin: Source.JudgmentSyntactic,
  +m: R.Micro, +r: P.Request, +ctx: D.Context,
  aut: {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>}, judgment: Source.JudgmentRefused(source, c, r, ctx)) ->
  Validation(source, c, s, origin, Q.concatenate(authenticated(m, r, Some{ctx}), [Q.Rejected{r, ctx}])):
  attach_mark(source, c, s, origin, authenticated(m, r, Some{ctx}), Q.Rejected{r, ctx},
    auth_validated(source, c, s, origin, m, r, Some{ctx}, Equal.sym(Maybe<&2, D.Context>, D.authenticate(s, I.credential(r)), Some{ctx}, aut)),
    L.Both{judgment, before_of_mark(authenticated(m, r, Some{ctx}), Q.Authenticated{r, Some{ctx}}, Q.Rejected{r, ctx}, index_auth(m, r), query_auth(m, r, Some{ctx}))})

def query_accepts(+m: R.Micro, +r: P.Request, +ctx: D.Context) ->
  {Q.query(verified(m, r, ctx), index_accepts(m, r, ctx)) == Some{Q.Accepts{r, ctx}} : Maybe<&2, Q.Frame>}:
  query_of_mark(authenticated(m, r, Some{ctx}), Q.Accepts{r, ctx})

def before_start(+m: R.Micro, +r: P.Request, +ctx: D.Context) -> List<&2, Q.Frame>:
  Q.concatenate(verified(m, r, ctx), R.micro_execution(m))

def starts_two(~source: Source.Source, -c: S.Configuration, -s: D.State, +origin: Source.JudgmentSyntactic,
  +m: R.Micro, +r: P.Request, +ctx: D.Context,
  auts: L.E<{D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>}, {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>}>,
  judgment: Source.JudgmentAccepted(source, c, r, ctx, origin)) -> Validation(source, c, s, origin, Con{Q.Configured{}, R.render_started(m, r, ctx)}):
  match auts:
    case L.Both{one, two}:
      %Q.concatenate_assoc(verified(m, r, ctx), R.micro_execution(m), [Q.Started{r, ctx}]) : Validation(source, c, s, origin, _)
      attach_mark(source, c, s, origin, before_start(m, r, ctx), Q.Started{r, ctx},
        attach_neutral(source, c, s, origin, verified(m, r, ctx), R.micro_execution(m), accepts_validated(source, c, s, origin, m, r, ctx, one, judgment), micro_execution_neutral(m)),
        L.Both{two, L.Both{
          before_of_mark(before_start(m, r, ctx), Q.Authenticated{r, Some{ctx}}, Q.Started{r, ctx}, index_auth(m, r),
            query_prefix(verified(m, r, ctx), R.micro_execution(m), index_auth(m, r), Q.Authenticated{r, Some{ctx}},
              query_prefix(authenticated(m, r, Some{ctx}), [Q.Accepts{r, ctx}], index_auth(m, r), Q.Authenticated{r, Some{ctx}}, query_auth(m, r, Some{ctx})))),
          before_of_mark(before_start(m, r, ctx), Q.Accepts{r, ctx}, Q.Started{r, ctx}, index_accepts(m, r, ctx),
            query_prefix(verified(m, r, ctx), R.micro_execution(m), index_accepts(m, r, ctx), Q.Accepts{r, ctx}, query_accepts(m, r, ctx)))}})

def starts_validated(~source: Source.Source, -c: S.Configuration, -s: D.State, +origin: Source.JudgmentSyntactic,
  +m: R.Micro, +r: P.Request, +ctx: D.Context,
  aut: {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>}, judgment: Source.JudgmentAccepted(source, c, r, ctx, origin)) -> Validation(source, c, s, origin, Con{Q.Configured{}, R.render_started(m, r, ctx)}):
  starts_two(source, c, s, origin, m, r, ctx, Q.equality_reopenable(Maybe<&2, D.Context>, D.authenticate(s, I.credential(r)), Some{ctx}, aut), judgment)

def two_associations(+xs: List<&2, Q.Frame>, +ys: List<&2, Q.Frame>, -q: Q.Frame, +zs: List<&2, Q.Frame>) ->
  {Q.concatenate(Q.concatenate(xs, Q.concatenate(ys, [q])), zs) == Q.concatenate(xs, Q.concatenate(ys, Con{q, zs})) : List<&2, Q.Frame>}:
  Equal.trans(List<&2, Q.Frame>, Q.concatenate(Q.concatenate(xs, Q.concatenate(ys, [q])), zs),
    Q.concatenate(xs, Q.concatenate(Q.concatenate(ys, [q]), zs)), Q.concatenate(xs, Q.concatenate(ys, Con{q, zs})),
    Q.concatenate_assoc(xs, Q.concatenate(ys, [q]), zs),
    Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, rest => Q.concatenate(xs, rest), Q.concatenate(Q.concatenate(ys, [q]), zs), Q.concatenate(ys, Con{q, zs}), Q.concatenate_assoc(ys, [q], zs)))

def resume_auth(~source: Source.Source, -c: S.Configuration, -s: D.State, +origin: Source.JudgmentSyntactic,
  +m: R.Micro, +r: P.Request, +ctx: Maybe<&2, D.Context>, +rest: List<&2, Q.Frame>,
  validated: Validation(source, c, s, origin, authenticated(m, r, ctx)), neutral: Neutral(rest)) ->
  Validation(source, c, s, origin, Q.concatenate(received(m, r), Q.concatenate(R.micro_authentication(m), Con{Q.Authenticated{r, ctx}, rest}))):
  %two_associations(received(m, r), R.micro_authentication(m), Q.Authenticated{r, ctx}, rest) : Validation(source, c, s, origin, _)
  attach_neutral(source, c, s, origin, authenticated(m, r, ctx), rest, validated, neutral)

def resume_mark(~source: Source.Source, -c: S.Configuration, -s: D.State, +origin: Source.JudgmentSyntactic,
  +xs: List<&2, Q.Frame>, +mark: Q.Frame, +rest: List<&2, Q.Frame>, validated: Validation(source, c, s, origin, Q.concatenate(xs, [mark])), neutral: Neutral(rest)) -> Validation(source, c, s, origin, Q.concatenate(xs, Con{mark, rest})):
  %Q.concatenate_assoc(xs, [mark], rest) : Validation(source, c, s, origin, _)
  attach_neutral(source, c, s, origin, Q.concatenate(xs, [mark]), rest, validated, neutral)

def prepared_neutral(p: N.Prepared) -> {neutral(R.frame_prepared(p)) == True{} : Bool}:
  match p:
    case N.Prepared{w, ts, r, bs}: {==}

def exec_validated(~source: Source.Source, -c: S.Configuration, -s: D.State, +origin: Source.JudgmentSyntactic,
  +m: R.Micro, +r: P.Request, +ctx: D.Context, +xs: List<&2, Q.FrameExec>, aut: {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>}, judgment: Source.JudgmentAccepted(source, c, r, ctx, origin)) -> Validation(source, c, s, origin, Con{Q.Configured{}, R.render_execution(m, r, ctx, xs)}):
  attach_neutral(source, c, s, origin, Con{Q.Configured{}, R.render_started(m, r, ctx)}, Q.expand_exec(r, ctx, xs), starts_validated(source, c, s, origin, m, r, ctx, aut, judgment), execution_neutral(r, ctx, xs))

def phase_validated(~source: Source.Source, -c: S.Configuration, +s: D.State, +origin: Source.JudgmentSyntactic,
  +m: R.Micro, phase: R.PhaseBefore, aut: Five.AuthOfPhase(s, phase), judgment: Source.JudgmentOfPhase(source, c, origin, phase)) -> Validation(source, c, s, origin, Con{Q.Configured{}, R.render_phase(m, phase)}):
  match phase:
    case R.BeforeInput{}: validate_neutral(source, c, s, origin, Con{Q.Configured{}, R.micro_input(m)}, L.Both{{==}, micro_input_neutral(m)})
    case R.AfterReceive{+r}: validate_neutral(source, c, s, origin, received(m, r), received_neutral(m, r))
    case R.AfterAuthenticate{+r, +ctx}: auth_validated(source, c, s, origin, m, r, Some{ctx}, Equal.sym(Maybe<&2, D.Context>, D.authenticate(s, I.credential(r)), Some{ctx}, aut))
    case R.AfterVerify{+r, +ctx}: accepts_validated(source, c, s, origin, m, r, ctx, aut, judgment)
    case R.Executing{+r, +ctx, +xs}: exec_validated(source, c, s, origin, m, r, ctx, xs, aut, judgment)
    case R.AfterPrepare{+r, +ctx, +xs, +p}:
      attach_neutral(source, c, s, origin, Con{Q.Configured{}, R.render_execution(m, r, ctx, xs)}, Q.concatenate(R.micro_output(m), [R.frame_prepared(p)]),
        exec_validated(source, c, s, origin, m, r, ctx, xs, aut, judgment),
        neutral_concatenated(R.micro_output(m), [R.frame_prepared(p)], micro_output_neutral(m), L.Both{prepared_neutral(p), Unit{}}))

def branch_validated(~source: Source.Source, -c: S.Configuration, +s: D.State, +origin: Source.JudgmentSyntactic,
  +m: R.Micro, branch: R.Branch, aut: Five.AuthOfBranch(s, branch), judgment: Source.JudgmentOfBranch(source, c, origin, branch)) -> Validation(source, c, s, origin, R.render(m, s, branch)):
  match branch:
    case R.InitialOk{}:
      validate_neutral(source, c, s, origin, R.render(m, s, R.InitialOk{}), L.Both{{==}, L.Both{{==}, neutral_concatenated(R.micro_output(m), R.render_initial(P.encode(D.state_value(s)), s), micro_output_neutral(m), initial_neutral(P.encode(D.state_value(s)), s))}})
    case R.InitialRefusal{status}: validate_neutral(source, c, s, origin, R.render(m, s, R.InitialRefusal{status}), L.Both{{==}, L.Both{{==}, Unit{}}})
    case R.InitialFailure{+accepts, +stage, +id, +fatal}:
      validate_neutral(source, c, s, origin, R.render(m, s, R.InitialFailure{accepts, stage, id, fatal}), L.Both{{==}, neutral_concatenated(R.prefix_initial(m, accepts), [Q.Failed{stage, id, fatal}, Q.InitialRefused{S.Failure{}}], prefix_initial_neutral(m, accepts), L.Both{{==}, L.Both{{==}, Unit{}}})})
    case R.WithoutResponse{}: validate_neutral(source, c, s, origin, R.render(m, s, R.WithoutResponse{}), L.Both{{==}, L.Both{{==}, Unit{}}})
    case R.InputRefusal{+error, +closes, +delivery}:
      validate_neutral(source, c, s, origin, R.render(m, s, R.InputRefusal{error, closes, delivery}), L.Both{{==}, neutral_concatenated(R.micro_input(m), R.render_error(R.status_input(error), s, closes, delivery), micro_input_neutral(m), error_neutral(R.status_input(error), s, closes, delivery))})
    case R.AutRefusal{+r, +delivery}:
      resume_auth(source, c, s, origin, m, r, None{}, R.render_error(S.Authentication{}, s, False{}, delivery),
        auth_validated(source, c, s, origin, m, r, None{}, Equal.sym(Maybe<&2, D.Context>, D.authenticate(s, I.credential(r)), None{}, aut)), error_neutral(S.Authentication{}, s, False{}, delivery))
    case R.GateRefusal{+r, +ctx, +delivery}:
      resume_mark(source, c, s, origin, authenticated(m, r, Some{ctx}), Q.Rejected{r, ctx}, R.render_error(S.Certificate{}, s, False{}, delivery), rejects_validated(source, c, s, origin, m, r, ctx, aut, judgment), error_neutral(S.Certificate{}, s, False{}, delivery))
    case R.Executed{+r, +ctx, +xs, +p, +delivery}:
      attach_neutral(source, c, s, origin, Con{Q.Configured{}, R.render_execution(m, r, ctx, xs)}, Q.concatenate(R.micro_output(m), R.render_final(p, s, False{}, delivery)), exec_validated(source, c, s, origin, m, r, ctx, xs, aut, judgment),
        neutral_concatenated(R.micro_output(m), R.render_final(p, s, False{}, delivery), micro_output_neutral(m), conclusion_neutral(N.conclude(p, s), False{}, delivery)))
    case R.FailureBefore{+phase, +stage, +id, +fatal, +delivery}:
      attach_neutral(source, c, s, origin, Con{Q.Configured{}, R.render_phase(m, phase)}, R.render_failure(s, stage, id, fatal, delivery), phase_validated(source, c, s, origin, m, phase, aut, judgment), failure_neutral(s, stage, id, fatal, delivery))
    case R.FatalAfterPublication{+r, +ctx, +xs, +p, +stage, +id}:
      attach_neutral(source, c, s, origin, Con{Q.Configured{}, R.render_execution(m, r, ctx, xs)}, Q.concatenate(R.micro_output(m), R.render_fatal_published(N.conclude(p, s), stage, id)), exec_validated(source, c, s, origin, m, r, ctx, xs, aut, judgment),
        neutral_concatenated(R.micro_output(m), R.render_fatal_published(N.conclude(p, s), stage, id), micro_output_neutral(m), fatal_neutral(N.conclude(p, s), stage, id)))
    case R.Pending{phase}: phase_validated(source, c, s, origin, m, phase, aut, judgment)
    case R.InitialPending{+accepts}: validate_neutral(source, c, s, origin, R.render(m, s, R.InitialPending{accepts}), L.Both{{==}, prefix_initial_neutral(m, accepts)})

# Three possible predecessors; all are facts of the same fixed trace.
type Predecessor is Data:
  RequestPrevious{r: P.Request}
  AutPrevious{r: P.Request, ctx: D.Context}
  CertPrevious{r: P.Request, ctx: D.Context}

def frame_previous(pre: Predecessor) -> Q.Frame:
  match pre:
    case RequestPrevious{r}: Q.Received{r}
    case AutPrevious{r, ctx}: Q.Authenticated{r, Some{ctx}}
    case CertPrevious{r, ctx}: Q.Accepts{r, ctx}

def fact_previous(~source: Source.Source, +origin: Source.JudgmentSyntactic, pre: Predecessor) -> I.Fact:
  match pre:
    case RequestPrevious{r}: I.ReceivedRequest{r}
    case AutPrevious{r, ctx}: I.Authenticated{r, Some{ctx}}
    case CertPrevious{r, ctx}: I.CertificateAccepted{r, ctx, Source.program(source, origin)}

def observation_previous(~source: Source.Source, -c: S.Configuration, -s: D.State, +origin: Source.JudgmentSyntactic,
  +xs: List<&2, Q.Frame>, +t: Nat, pre: Predecessor,
  query_result: {Q.query(xs, t) == Some{frame_previous(pre)} : Maybe<&2, Q.Frame>}) ->
  Q.observes_service(c, Source.program(source, origin), Some{s}, xs, t, fact_previous(source, origin, pre)):
  match pre:
    case RequestPrevious{+r}: Q.query_establishes_observation(c, Source.program(source, origin), xs, t, Q.Received{r}, I.ReceivedRequest{r}, query_result, {==})
    case AutPrevious{+r, +ctx}: Q.query_establishes_observation(c, Source.program(source, origin), xs, t, Q.Authenticated{r, Some{ctx}}, I.Authenticated{r, Some{ctx}}, query_result, {==})
    case CertPrevious{+r, +ctx}: Q.query_establishes_observation(c, Source.program(source, origin), xs, t, Q.Accepts{r, ctx}, I.CertificateAccepted{r, ctx, Source.program(source, origin)}, query_result, {==})

def Lift(~source: Source.Source, -x: I.Scenario, +origin: Source.JudgmentSyntactic, -xs: List<&2, Q.Frame>) -> Type:
  @u: Nat -> @pre: Predecessor -> {Q.query(xs, u) == Some{frame_previous(pre)} : Maybe<&2, Q.Frame>} ->
    I.Happens(Source.environment(source), Source.artifact(source), x, u, fact_previous(source, origin, pre))

def before_in_environment(~source: Source.Source, -x: I.Scenario, +origin: Source.JudgmentSyntactic,
  -xs: List<&2, Q.Frame>, -t: Nat, +pre: Predecessor, lift: Lift(source, x, origin, xs), before: Before(xs, t, frame_previous(pre))) ->
  I.Before(Source.environment(source), Source.artifact(source), x, t, fact_previous(source, origin, pre)):
  match before:
    case (+u, L.Both{order, query_result}): (u, L.Both{order, lift(u, pre, query_result)})

# Functions below consume the sole actual query. They receive no Rule3/4.
def rule3_raw(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +reception: X.Reception,
  +origin: Source.JudgmentSyntactic, +xs: List<&2, Q.Frame>, +t: Nat, f: I.Fact,
  is_valid: Validation(source, c, s, origin, xs), lift: Lift(source, I.Serve{world, c, s, reception}, origin, xs),
  fact: Q.observes_service(c, Source.program(source, origin), Some{s}, xs, t, f)) ->
  K.Rule3(f, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t):
  match f:
    case I.Authenticated{+r, +ctx}:
      F.combined_pair(K.Rule3(I.Authenticated{r, ctx}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t),
        Content(source, c, s, origin, Q.Authenticated{r, ctx}), Order(xs, t, Q.Authenticated{r, ctx}),
        is_valid(t, Q.Authenticated{r, ctx}, Q.observation_frame(c, Source.program(source, origin), xs, t, I.Authenticated{r, ctx}, fact)),
        content => order => L.Both{content, before_in_environment(source, I.Serve{world, c, s, reception}, origin, xs, t, RequestPrevious{r}, lift, order)})
    case I.ProgramStarted{+r, +ctx, p}:
      F.combined_pair(K.Rule3(I.ProgramStarted{r, ctx, p}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t),
        Content(source, c, s, origin, Q.Started{r, ctx}), Order(xs, t, Q.Started{r, ctx}),
        is_valid(t, Q.Started{r, ctx}, Q.observation_frame(c, Source.program(source, origin), xs, t, I.ProgramStarted{r, ctx, p}, fact)),
        content => order => L.Both{content, before_in_environment(source, I.Serve{world, c, s, reception}, origin, xs, t, AutPrevious{r, ctx}, lift,
          L.and_left(Before(xs, t, Q.Authenticated{r, Some{ctx}}), Before(xs, t, Q.Accepts{r, ctx}), order))})
    case I.ConfigurationInUse{a0}: Unit{}
    case I.InspectionNotModeled{a0}: Unit{}
    case I.EffectNotModeled{a0}: Unit{}
    case I.InstanceStarted{a0}: Unit{}
    case I.InitializationRefused{a0}: Unit{}
    case I.ProofInitialAccepts{}: Unit{}
    case I.Encoded{a0, a1}: Unit{}
    case I.Decoded{a0, a1}: Unit{}
    case I.Stored{a0, a1, a2}: Unit{}
    case I.Operated{a0, a1, a2, a3}: Unit{}
    case I.CheckedLength{a0, a1}: Unit{}
    case I.AllocatedField{a0, a1}: Unit{}
    case I.ReadBody{a0, a1, a2}: Unit{}
    case I.ReceivedRequest{a0}: Unit{}
    case I.CertificateAccepted{a0, a1, a2}: Unit{}
    case I.CertificateRejected{a0, a1}: Unit{}
    case I.Evaluated{a0, a1, a2, a3}: Unit{}
    case I.Prepared{a0, a1}: Unit{}
    case I.Published{a0}: Unit{}
    case I.StateVisible{a0}: Unit{}
    case I.FailedEnvironment{a0, a1, a2}: Unit{}
    case I.Concluded{a0, a1, a2}: Unit{}
    case I.DeliveredEverything{a0}: Unit{}
    case I.DeliveryInterrupted{a0}: Unit{}
    case I.ClosedChannel{}: Unit{}
    case I.NextCall{a0, a1}: Unit{}

def fact_of_same_source(~source: Source.Source, -c: S.Configuration, +origin: Source.JudgmentSyntactic,
  +xs: List<&2, Q.Frame>, +t: Nat, +q: Q.Frame, -f: I.Fact, -expected: I.Fact,
  fact: Q.observes(c, Source.program(source, origin), xs, t, f),
  query_result: {Q.query(xs, t) == Some{q} : Maybe<&2, Q.Frame>}, relation: Q.rel_fact(c, Source.program(source, origin), q, expected)) -> {f == expected : I.Fact}:
  Q.observation_unique(c, Source.program(source, origin), xs, t, f, expected, fact,
    Q.query_establishes_observation(c, Source.program(source, origin), xs, t, q, expected, query_result, relation))

def accepts4_data(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +reception: X.Reception,
  +origin: Source.JudgmentSyntactic, +xs: List<&2, Q.Frame>, +t: Nat, +r: P.Request, +ctx: D.Context, -p: S.Program,
  data: FrameFacts(source, c, s, origin, xs, t, Q.Accepts{r, ctx}), lift: Lift(source, I.Serve{world, c, s, reception}, origin, xs),
  same: {I.CertificateAccepted{r, ctx, p} == I.CertificateAccepted{r, ctx, Source.program(source, origin)} : I.Fact}) ->
  K.Rule4(I.CertificateAccepted{r, ctx, p}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t):
  %Equal.sym(I.Fact, I.CertificateAccepted{r, ctx, p}, I.CertificateAccepted{r, ctx, Source.program(source, origin)}, same) :
    K.Rule4(_, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t)
  F.combined_pair(K.Rule4(I.CertificateAccepted{r, ctx, Source.program(source, origin)}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t),
    Content(source, c, s, origin, Q.Accepts{r, ctx}), Order(xs, t, Q.Accepts{r, ctx}), data,
    content => order => L.Both{before_in_environment(source, I.Serve{world, c, s, reception}, origin, xs, t, AutPrevious{r, ctx}, lift, order), content})

def starts4_data(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +reception: X.Reception,
  +origin: Source.JudgmentSyntactic, +xs: List<&2, Q.Frame>, +t: Nat, +r: P.Request, +ctx: D.Context, -p: S.Program,
  data: FrameFacts(source, c, s, origin, xs, t, Q.Started{r, ctx}), lift: Lift(source, I.Serve{world, c, s, reception}, origin, xs),
  same: {I.ProgramStarted{r, ctx, p} == I.ProgramStarted{r, ctx, Source.program(source, origin)} : I.Fact}) ->
  K.Rule4(I.ProgramStarted{r, ctx, p}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t):
  %Equal.sym(I.Fact, I.ProgramStarted{r, ctx, p}, I.ProgramStarted{r, ctx, Source.program(source, origin)}, same) :
    K.Rule4(_, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t)
  F.combined_pair(K.Rule4(I.ProgramStarted{r, ctx, Source.program(source, origin)}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t),
    Content(source, c, s, origin, Q.Started{r, ctx}), Order(xs, t, Q.Started{r, ctx}), data,
    content => order => before_in_environment(source, I.Serve{world, c, s, reception}, origin, xs, t, CertPrevious{r, ctx}, lift,
      L.and_right(Before(xs, t, Q.Authenticated{r, Some{ctx}}), Before(xs, t, Q.Accepts{r, ctx}), order)))

def accepts4_queries(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +reception: X.Reception,
  +origin: Source.JudgmentSyntactic, +xs: List<&2, Q.Frame>, +t: Nat, +r: P.Request, +ctx: D.Context, -p: S.Program,
  is_valid: Validation(source, c, s, origin, xs), lift: Lift(source, I.Serve{world, c, s, reception}, origin, xs),
  fact: Q.observes(c, Source.program(source, origin), xs, t, I.CertificateAccepted{r, ctx, p}),
  queries: L.E<{Q.query(xs, t) == Some{Q.Accepts{r, ctx}} : Maybe<&2, Q.Frame>}, {Q.query(xs, t) == Some{Q.Accepts{r, ctx}} : Maybe<&2, Q.Frame>}>) ->
  K.Rule4(I.CertificateAccepted{r, ctx, p}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t):
  match queries:
    case L.Both{one, two}: accepts4_data(source, c, world, s, reception, origin, xs, t, r, ctx, p, is_valid(t, Q.Accepts{r, ctx}, one), lift,
      fact_of_same_source(source, c, origin, xs, t, Q.Accepts{r, ctx}, I.CertificateAccepted{r, ctx, p}, I.CertificateAccepted{r, ctx, Source.program(source, origin)}, fact, two, {==}))

def starts4_queries(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +reception: X.Reception,
  +origin: Source.JudgmentSyntactic, +xs: List<&2, Q.Frame>, +t: Nat, +r: P.Request, +ctx: D.Context, -p: S.Program,
  is_valid: Validation(source, c, s, origin, xs), lift: Lift(source, I.Serve{world, c, s, reception}, origin, xs),
  fact: Q.observes(c, Source.program(source, origin), xs, t, I.ProgramStarted{r, ctx, p}),
  queries: L.E<{Q.query(xs, t) == Some{Q.Started{r, ctx}} : Maybe<&2, Q.Frame>}, {Q.query(xs, t) == Some{Q.Started{r, ctx}} : Maybe<&2, Q.Frame>}>) ->
  K.Rule4(I.ProgramStarted{r, ctx, p}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t):
  match queries:
    case L.Both{one, two}: starts4_data(source, c, world, s, reception, origin, xs, t, r, ctx, p, is_valid(t, Q.Started{r, ctx}, one), lift,
      fact_of_same_source(source, c, origin, xs, t, Q.Started{r, ctx}, I.ProgramStarted{r, ctx, p}, I.ProgramStarted{r, ctx, Source.program(source, origin)}, fact, two, {==}))

def rule4_raw(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +reception: X.Reception,
  +origin: Source.JudgmentSyntactic, +xs: List<&2, Q.Frame>, +t: Nat, f: I.Fact,
  is_valid: Validation(source, c, s, origin, xs), lift: Lift(source, I.Serve{world, c, s, reception}, origin, xs),
  fact: Q.observes_service(c, Source.program(source, origin), Some{s}, xs, t, f)) ->
  K.Rule4(f, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t):
  match f:
    case I.CertificateAccepted{+r, +ctx, p}:
      F.combined_pair(K.Rule4(I.CertificateAccepted{r, ctx, p}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t),
        Q.observes(c, Source.program(source, origin), xs, t, I.CertificateAccepted{r, ctx, p}), Q.observes(c, Source.program(source, origin), xs, t, I.CertificateAccepted{r, ctx, p}),
        Q.duplicate_observation(c, Source.program(source, origin), xs, t, I.CertificateAccepted{r, ctx, p}, fact), one => two =>
          accepts4_queries(source, c, world, s, reception, origin, xs, t, r, ctx, p, is_valid, lift, one,
            Q.equality_reopenable(Maybe<&2, Q.Frame>, Q.query(xs, t), Some{Q.Accepts{r, ctx}}, Q.observation_frame(c, Source.program(source, origin), xs, t, I.CertificateAccepted{r, ctx, p}, two))))
    case I.CertificateRejected{+r, +ctx}:
      F.combined_pair(K.Rule4(I.CertificateRejected{r, ctx}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t),
        Content(source, c, s, origin, Q.Rejected{r, ctx}), Order(xs, t, Q.Rejected{r, ctx}),
        is_valid(t, Q.Rejected{r, ctx}, Q.observation_frame(c, Source.program(source, origin), xs, t, I.CertificateRejected{r, ctx}, fact)),
        content => order => L.Both{before_in_environment(source, I.Serve{world, c, s, reception}, origin, xs, t, AutPrevious{r, ctx}, lift, order), content})
    case I.ProgramStarted{+r, +ctx, p}:
      F.combined_pair(K.Rule4(I.ProgramStarted{r, ctx, p}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t),
        Q.observes(c, Source.program(source, origin), xs, t, I.ProgramStarted{r, ctx, p}), Q.observes(c, Source.program(source, origin), xs, t, I.ProgramStarted{r, ctx, p}),
        Q.duplicate_observation(c, Source.program(source, origin), xs, t, I.ProgramStarted{r, ctx, p}, fact), one => two =>
          starts4_queries(source, c, world, s, reception, origin, xs, t, r, ctx, p, is_valid, lift, one,
            Q.equality_reopenable(Maybe<&2, Q.Frame>, Q.query(xs, t), Some{Q.Started{r, ctx}}, Q.observation_frame(c, Source.program(source, origin), xs, t, I.ProgramStarted{r, ctx, p}, two))))
    case I.ConfigurationInUse{a0}: Unit{}
    case I.InspectionNotModeled{a0}: Unit{}
    case I.EffectNotModeled{a0}: Unit{}
    case I.InstanceStarted{a0}: Unit{}
    case I.InitializationRefused{a0}: Unit{}
    case I.ProofInitialAccepts{}: Unit{}
    case I.Encoded{a0, a1}: Unit{}
    case I.Decoded{a0, a1}: Unit{}
    case I.Stored{a0, a1, a2}: Unit{}
    case I.Operated{a0, a1, a2, a3}: Unit{}
    case I.CheckedLength{a0, a1}: Unit{}
    case I.AllocatedField{a0, a1}: Unit{}
    case I.ReadBody{a0, a1, a2}: Unit{}
    case I.ReceivedRequest{a0}: Unit{}
    case I.Authenticated{a0, a1}: Unit{}
    case I.Evaluated{a0, a1, a2, a3}: Unit{}
    case I.Prepared{a0, a1}: Unit{}
    case I.Published{a0}: Unit{}
    case I.StateVisible{a0}: Unit{}
    case I.FailedEnvironment{a0, a1, a2}: Unit{}
    case I.Concluded{a0, a1, a2}: Unit{}
    case I.DeliveredEverything{a0}: Unit{}
    case I.DeliveryInterrupted{a0}: Unit{}
    case I.ClosedChannel{}: Unit{}
    case I.NextCall{a0, a1}: Unit{}

type WhichLaw is Data:
  AuthenticationLaw{}
  AdmissionLaw{}

def Rule(rule: WhichLaw, f: I.Fact, -a: I.Environment, -k: String, -x: I.Scenario, -t: Nat) -> Type:
  match rule:
    case AuthenticationLaw{}: K.Rule3(f, a, k, x, t)
    case AdmissionLaw{}: K.Rule4(f, a, k, x, t)

def rule_raw(~source: Source.Source, ~c: S.Configuration, rule: WhichLaw, +world: Nat, +s: D.State, +reception: X.Reception,
  +origin: Source.JudgmentSyntactic, +xs: List<&2, Q.Frame>, +t: Nat, f: I.Fact,
  is_valid: Validation(source, c, s, origin, xs), lift: Lift(source, I.Serve{world, c, s, reception}, origin, xs),
  fact: Q.observes_service(c, Source.program(source, origin), Some{s}, xs, t, f)) ->
  Rule(rule, f, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t):
  match rule:
    case AuthenticationLaw{}: rule3_raw(source, c, world, s, reception, origin, xs, t, f, is_valid, lift, fact)
    case AdmissionLaw{}: rule4_raw(source, c, world, s, reception, origin, xs, t, f, is_valid, lift, fact)

# One call to the existing selector produces authentication equality.
def aut_of_decision(~source: Source.Source, ~c: S.Configuration, +s: D.State, +origin: Source.JudgmentSyntactic,
  +state: List<&2, U32>, +data: R.DataTools, +reception: X.Reception,
  real: Five.FramingReal(source, c, s, origin, state, S.schema(c), S.limits(c), data,
    X.decide_reception_in(S.limits(c), reception), R.preprocessing(data))) -> Five.AuthOfBranch(s, R.decide(c, reception, state, data)):
  L.and_left(Five.AuthOfBranch(s, R.decide(c, reception, state, data)), Five.GateOfBranch(R.judgment_of(data), R.decide(c, reception, state, data)),
    L.and_right(Five.BranchReal(source, c, s, origin, R.decide(c, reception, state, data)),
      L.E<Five.AuthOfBranch(s, R.decide(c, reception, state, data)), Five.GateOfBranch(R.judgment_of(data), R.decide(c, reception, state, data))>,
      Five.route_real_decided(source, c, s, origin, state, data, reception, real)))

def OriginCall(~source: Source.Source, ~c: S.Configuration, +s: D.State, +reception: X.Reception,
  data: Source.CallData) -> Type:
  match data:
    case Source.CallData{cf, +ps, pf, tf, +state, +tools, micro}:
      L.E<Five.CallReal(source, c, s, reception, Source.CallData{cf, ps, pf, tf, state, tools, micro}),
        Source.JudgmentOfBranch(source, c, ps, R.decide(c, reception, state, tools))>

def introduce_of_call(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +reception: X.Reception,
  +cf: Source.JudgmentSyntactic, +origin: Source.JudgmentSyntactic, +pf: Source.JudgmentSyntactic, +tf: Source.JudgmentSyntactic,
  +state: List<&2, U32>, +data: R.DataTools, +micro: R.Micro, +u: Nat, +pre: Predecessor,
  canonical: {I.Serve{world, c, s, reception} == Source.scenario(source, world) : I.Scenario},
  metadata: {Source.call(source, world) == Source.CallData{cf, origin, pf, tf, state, data, micro} : Source.CallData},
  query_result: {Q.query(R.generate(c, reception, state, s, data, micro), u) == Some{frame_previous(pre)} : Maybe<&2, Q.Frame>}) ->
  I.Happens(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, u, fact_previous(source, origin, pre)):
  Source.introduce_fact_literal(source, Source.artifact(source), I.Serve{world, c, s, reception}, u, fact_previous(source, origin, pre),
    L.Both{{==}, L.Both{canonical,
      (%Equal.sym(Source.CallData, Source.call(source, world), Source.CallData{cf, origin, pf, tf, state, data, micro}, metadata) :
        Source.of_observation(source, c, Source.construct_call(c, s, reception, _), u, fact_previous(source, origin, pre))
      observation_previous(source, c, s, origin, R.generate(c, reception, state, s, data, micro), u, pre, query_result))}})

def rule_of_call(~source: Source.Source, ~c: S.Configuration, rule: WhichLaw,
  +world: Nat, +s: D.State, +reception: X.Reception, data: Source.CallData,
  +t: Nat, f: I.Fact, canonical: {I.Serve{world, c, s, reception} == Source.scenario(source, world) : I.Scenario},
  origins: L.E<{Source.call(source, world) == data : Source.CallData}, {Source.call(source, world) == data : Source.CallData}>,
  real: OriginCall(source, c, s, reception, data), fact: Source.of_route(source, I.Serve{world, c, s, reception}, t, f)) ->
  Rule(rule, f, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t):
  match data origins real:
    case Source.CallData{+cf, +origin, +pf, +tf, +state, +tools, +micro} L.Both{read, replace} L.Both{execution, judgment}:
      rule_raw(source, c, rule, world, s, reception, origin, R.generate(c, reception, state, s, tools, micro), t, f,
        branch_validated(source, c, s, origin, micro, R.decide(c, reception, state, tools), aut_of_decision(source, c, s, origin, state, tools, reception, execution), judgment),
        +u => +pre => query_result => introduce_of_call(source, c, world, s, reception, cf, origin, pf, tf, state, tools, micro, u, pre, canonical, replace, query_result),
        (%read : Source.of_observation(source, c, Source.construct_call(c, s, reception, _), t, f) fact))

def initial_result_neutral(+m: R.Micro, +s: D.State, j: R.Judgment, result: R.ResultInitial, +is_valid: Bool) -> Neutral(R.render(m, s, R.decide_judgment_initial(j, result, is_valid))):
  match j:
    case R.Accepted{}:
      match result:
        case R.InitializationFinished{}:
          match is_valid:
            case False{}: L.Both{{==}, L.Both{{==}, Unit{}}}
            case True{}: L.Both{{==}, L.Both{{==}, neutral_concatenated(R.micro_output(m), R.render_initial(P.encode(D.state_value(s)), s), micro_output_neutral(m), initial_neutral(P.encode(D.state_value(s)), s))}}
        case R.FailedInitial{+accepts, +stage, +id, +fatal}: L.Both{{==}, neutral_concatenated(R.prefix_initial(m, accepts && is_valid), [Q.Failed{stage, id, fatal}, Q.InitialRefused{S.Failure{}}], prefix_initial_neutral(m, accepts && is_valid), L.Both{{==}, L.Both{{==}, Unit{}}})}
        case R.PendingInitial{accepts}: L.Both{{==}, prefix_initial_neutral(m, accepts && is_valid)}
    case R.Refused{}: L.Both{{==}, L.Both{{==}, Unit{}}}
    case R.ErrorJudgment{id, fatal}: L.Both{{==}, L.Both{{==}, L.Both{{==}, Unit{}}}}
    case R.PendingJudgment{}: L.Both{{==}, Unit{}}

def rule3_initial(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +pi: String,
  +xs: List<&2, Q.Frame>, +t: Nat, f: I.Fact, neutral: Neutral(xs), fact: Q.observes_service(c, Source.without_program(), None{}, xs, t, f)) ->
  K.Rule3(f, Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t):
  match f:
    case I.ConfigurationInUse{a0}: Unit{}
    case I.InspectionNotModeled{a0}: Unit{}
    case I.EffectNotModeled{a0}: Unit{}
    case I.InstanceStarted{a0}: Unit{}
    case I.InitializationRefused{a0}: Unit{}
    case I.ProofInitialAccepts{}: Unit{}
    case I.Encoded{a0, a1}: Unit{}
    case I.Decoded{a0, a1}: Unit{}
    case I.Stored{a0, a1, a2}: Unit{}
    case I.Operated{a0, a1, a2, a3}: Unit{}
    case I.CheckedLength{a0, a1}: Unit{}
    case I.AllocatedField{a0, a1}: Unit{}
    case I.ReadBody{a0, a1, a2}: Unit{}
    case I.ReceivedRequest{a0}: Unit{}
    case I.Authenticated{a0, a1}: F.absurd_boolean(K.Rule3(I.Authenticated{a0, a1}, Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t),
      neutral_queried(xs, t, Q.Authenticated{a0, a1}, neutral, Q.observation_frame(c, Source.without_program(), xs, t, I.Authenticated{a0, a1}, fact)))
    case I.CertificateAccepted{a0, a1, a2}: Unit{}
    case I.CertificateRejected{a0, a1}: Unit{}
    case I.ProgramStarted{a0, a1, a2}: F.absurd_boolean(K.Rule3(I.ProgramStarted{a0, a1, a2}, Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t),
      neutral_queried(xs, t, Q.Started{a0, a1}, neutral, Q.observation_frame(c, Source.without_program(), xs, t, I.ProgramStarted{a0, a1, a2}, fact)))
    case I.Evaluated{a0, a1, a2, a3}: Unit{}
    case I.Prepared{a0, a1}: Unit{}
    case I.Published{a0}: Unit{}
    case I.StateVisible{a0}: Unit{}
    case I.FailedEnvironment{a0, a1, a2}: Unit{}
    case I.Concluded{a0, a1, a2}: Unit{}
    case I.DeliveredEverything{a0}: Unit{}
    case I.DeliveryInterrupted{a0}: Unit{}
    case I.ClosedChannel{}: Unit{}
    case I.NextCall{a0, a1}: Unit{}

def rule4_initial(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +pi: String,
  +xs: List<&2, Q.Frame>, +t: Nat, f: I.Fact, neutral: Neutral(xs), fact: Q.observes_service(c, Source.without_program(), None{}, xs, t, f)) ->
  K.Rule4(f, Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t):
  match f:
    case I.ConfigurationInUse{a0}: Unit{}
    case I.InspectionNotModeled{a0}: Unit{}
    case I.EffectNotModeled{a0}: Unit{}
    case I.InstanceStarted{a0}: Unit{}
    case I.InitializationRefused{a0}: Unit{}
    case I.ProofInitialAccepts{}: Unit{}
    case I.Encoded{a0, a1}: Unit{}
    case I.Decoded{a0, a1}: Unit{}
    case I.Stored{a0, a1, a2}: Unit{}
    case I.Operated{a0, a1, a2, a3}: Unit{}
    case I.CheckedLength{a0, a1}: Unit{}
    case I.AllocatedField{a0, a1}: Unit{}
    case I.ReadBody{a0, a1, a2}: Unit{}
    case I.ReceivedRequest{a0}: Unit{}
    case I.Authenticated{a0, a1}: Unit{}
    case I.CertificateAccepted{a0, a1, a2}: F.absurd_boolean(K.Rule4(I.CertificateAccepted{a0, a1, a2}, Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t),
      neutral_queried(xs, t, Q.Accepts{a0, a1}, neutral, Q.observation_frame(c, Source.without_program(), xs, t, I.CertificateAccepted{a0, a1, a2}, fact)))
    case I.CertificateRejected{a0, a1}: F.absurd_boolean(K.Rule4(I.CertificateRejected{a0, a1}, Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t),
      neutral_queried(xs, t, Q.Rejected{a0, a1}, neutral, Q.observation_frame(c, Source.without_program(), xs, t, I.CertificateRejected{a0, a1}, fact)))
    case I.ProgramStarted{a0, a1, a2}: F.absurd_boolean(K.Rule4(I.ProgramStarted{a0, a1, a2}, Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t),
      neutral_queried(xs, t, Q.Started{a0, a1}, neutral, Q.observation_frame(c, Source.without_program(), xs, t, I.ProgramStarted{a0, a1, a2}, fact)))
    case I.Evaluated{a0, a1, a2, a3}: Unit{}
    case I.Prepared{a0, a1}: Unit{}
    case I.Published{a0}: Unit{}
    case I.StateVisible{a0}: Unit{}
    case I.FailedEnvironment{a0, a1, a2}: Unit{}
    case I.Concluded{a0, a1, a2}: Unit{}
    case I.DeliveredEverything{a0}: Unit{}
    case I.DeliveryInterrupted{a0}: Unit{}
    case I.ClosedChannel{}: Unit{}
    case I.NextCall{a0, a1}: Unit{}

def rule_initial(~source: Source.Source, ~c: S.Configuration, rule: WhichLaw, +world: Nat, +s: D.State, +pi: String,
  +xs: List<&2, Q.Frame>, +t: Nat, f: I.Fact, neutral: Neutral(xs), fact: Q.observes_service(c, Source.without_program(), None{}, xs, t, f)) ->
  Rule(rule, f, Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t):
  match rule:
    case AuthenticationLaw{}: rule3_initial(source, c, world, s, pi, xs, t, f, neutral, fact)
    case AdmissionLaw{}: rule4_initial(source, c, world, s, pi, xs, t, f, neutral, fact)

def rule_data_initial(~source: Source.Source, ~c: S.Configuration, rule: WhichLaw,
  +world: Nat, +s: D.State, +pi: String, data: Source.InitialData, +t: Nat, f: I.Fact,
  metadata: {Source.initial(source, world) == data : Source.InitialData}, fact: Source.of_route(source, I.Initialize{world, c, s, pi}, t, f)) ->
  Rule(rule, f, Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t):
  match data:
    case Source.InitialData{cf, sf, pf, +j, +result, +micro}:
      rule_initial(source, c, rule, world, s, pi, R.generate_result_initial(c, Source.identity(source), s, j, result, micro), t, f,
        initial_result_neutral(micro, s, j, result, Config.is_valid(c, Source.identity(source))),
        (%metadata : Source.of_observation(source, c, Source.construct_initial(Source.identity(source), c, s, _), t, f) fact))

# Source contracts per world: actual executor/snapshot equations and
# both closed terms judged by the checker. No law is a premise.
def OriginOfMoment(~source: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, +world: Nat, moment: Scenarios.Moment) -> Type:
  match moment:
    case Scenarios.Initialization{}: Unit
    case Scenarios.Service{+reception}:
      OriginCall(source, c, History.state(history(world), seed(Unit{})), reception, Source.call(source, world))

def rule_by_moment(~source: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~pi: String, rule: WhichLaw, moment: Scenarios.Moment,
  +world: Nat, +t: Nat, f: I.Fact,
  canonical: {Scenarios.of_moment(c, seed, history, pi, moment, world) == Source.scenario(source, world) : I.Scenario},
  origin: OriginOfMoment(source, c, seed, history, world, moment),
  fact: Source.of_route(source, Scenarios.of_moment(c, seed, history, pi, moment, world), t, f)) ->
  Rule(rule, f, Source.environment(source), Source.artifact(source), Scenarios.of_moment(c, seed, history, pi, moment, world), t):
  match moment:
    case Scenarios.Initialization{}:
      rule_data_initial(source, c, rule, world, seed(Unit{}), pi, Source.initial(source, world), t, f, {==}, fact)
    case Scenarios.Service{+reception}:
      rule_of_call(source, c, rule, world, History.state(history(world), seed(Unit{})), reception, Source.call(source, world), t, f, canonical, L.Both{{==}, {==}}, origin, fact)

def rule_of_scenario(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moments: Nat -> Scenarios.Moment, ~pi: String,
  rule: WhichLaw, x: I.Scenario, +t: Nat, f: I.Fact,
  origins: @m: Nat -> OriginOfMoment(Model.source(base, c, seed, history, moments, pi), c, seed, history, m, moments(m)),
  fact: I.Happens(Source.environment(Model.source(base, c, seed, history, moments, pi)), Source.artifact(Model.source(base, c, seed, history, moments, pi)), x, t, f)) ->
  Rule(rule, f, Source.environment(Model.source(base, c, seed, history, moments, pi)), Source.artifact(Model.source(base, c, seed, history, moments, pi)), x, t):
  match x:
    case I.Initialize{+world, configuration, +s, +proof}:
      match fact:
        case L.Both{name, L.Both{equal, obs}}:
          %Equal.sym(I.Scenario, I.Initialize{world, configuration, s, proof}, Scenarios.canonical(c, seed, history, moments, pi, world),
            Equal.trans(I.Scenario, I.Initialize{world, configuration, s, proof}, Source.scenario(Model.source(base, c, seed, history, moments, pi), world),
              Scenarios.canonical(c, seed, history, moments, pi, world), equal, Model.scenario_of_model(base, c, seed, history, moments, pi, world))) :
            Rule(rule, f, Source.environment(Model.source(base, c, seed, history, moments, pi)), Source.artifact(Model.source(base, c, seed, history, moments, pi)), _, t)
          rule_by_moment(Model.source(base, c, seed, history, moments, pi), c, seed, history, pi, rule, moments(world), world, t, f,
            Equal.sym(I.Scenario, Source.scenario(Model.source(base, c, seed, history, moments, pi), world), Scenarios.canonical(c, seed, history, moments, pi, world), Model.scenario_of_model(base, c, seed, history, moments, pi, world)),
            origins(world), (%Model.scenario_of_model(base, c, seed, history, moments, pi, world) : Source.of_route(Model.source(base, c, seed, history, moments, pi), _, t, f) obs))
    case I.Serve{+world, configuration, +s, +reception}:
      match fact:
        case L.Both{name, L.Both{equal, obs}}:
          %Equal.sym(I.Scenario, I.Serve{world, configuration, s, reception}, Scenarios.canonical(c, seed, history, moments, pi, world),
            Equal.trans(I.Scenario, I.Serve{world, configuration, s, reception}, Source.scenario(Model.source(base, c, seed, history, moments, pi), world),
              Scenarios.canonical(c, seed, history, moments, pi, world), equal, Model.scenario_of_model(base, c, seed, history, moments, pi, world))) :
            Rule(rule, f, Source.environment(Model.source(base, c, seed, history, moments, pi)), Source.artifact(Model.source(base, c, seed, history, moments, pi)), _, t)
          rule_by_moment(Model.source(base, c, seed, history, moments, pi), c, seed, history, pi, rule, moments(world), world, t, f,
            Equal.sym(I.Scenario, Source.scenario(Model.source(base, c, seed, history, moments, pi), world), Scenarios.canonical(c, seed, history, moments, pi, world), Model.scenario_of_model(base, c, seed, history, moments, pi, world)),
            origins(world), (%Model.scenario_of_model(base, c, seed, history, moments, pi, world) : Source.of_route(Model.source(base, c, seed, history, moments, pi), _, t, f) obs))

law law3_of_model:
  for ~base: Source.Source
  for ~c: S.Configuration
  for ~seed: Unit -> D.State
  for ~history: Nat -> List<&2, History.Record>
  for ~moments: Nat -> Scenarios.Moment
  for ~pi: String
  for origins: @m: Nat -> OriginOfMoment(Model.source(base, c, seed, history, moments, pi), c, seed, history, m, moments(m))
  K.Law3(Source.environment(Model.source(base, c, seed, history, moments, pi)), Source.artifact(Model.source(base, c, seed, history, moments, pi)))
def law3_of_model(base, c, seed, history, moments, pi, origins):
  x => +t => f => fact => rule_of_scenario(base, c, seed, history, moments, pi, AuthenticationLaw{}, x, t, f, origins, fact)

law law4_of_model:
  for ~base: Source.Source
  for ~c: S.Configuration
  for ~seed: Unit -> D.State
  for ~history: Nat -> List<&2, History.Record>
  for ~moments: Nat -> Scenarios.Moment
  for ~pi: String
  for origins: @m: Nat -> OriginOfMoment(Model.source(base, c, seed, history, moments, pi), c, seed, history, m, moments(m))
  K.Law4(Source.environment(Model.source(base, c, seed, history, moments, pi)), Source.artifact(Model.source(base, c, seed, history, moments, pi)))
def law4_of_model(base, c, seed, history, moments, pi, origins):
  x => +t => f => fact => rule_of_scenario(base, c, seed, history, moments, pi, AdmissionLaw{}, x, t, f, origins, fact)
