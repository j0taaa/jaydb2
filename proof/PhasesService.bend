# Structural invariants of the protocol-generated ending.
import Base
import ./Publication.bend as U
import ./Preparation.bend as Preparation
import ./Call.bend as Call
import ./Proposal.bend as Proposal
import ./Configuration.bend as Configuration
import ../src/ConfigurationCheck.bend as Config
import ../contract/Requirements.bend as R
import ./ProtocolService.bend as Q
import ./RoutesService.bend as H
import ./PrimitivesService.bend as M
import ../src/State.bend as State
import ../contract/Protocol.bend as Protocol
import ../src/Codec.bend as C
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Logic.bend as L
import ../contract/Interface.bend as I
import ../contract/LAWS.bend as K
import ../contract/Resources.bend as X
import ./Foundations.bend as F
import ../src/Core.bend as N

type FrameKind is Data:
  RefusalInitial{}
  InspectionExternal{}
  EffectExternal{}
  StartWithProof{}
  Initialization{}
  Publication{}
  Conclusion{}
  Complete{}
  Interrupted{}

def classify(q: Q.Frame, kind: FrameKind) -> Bool:
  match q kind:
    case Q.InitialRefused{status} RefusalInitial{}: True{}
    case Q.Inspection{description} InspectionExternal{}: True{}
    case Q.Effect{description} EffectExternal{}: True{}
    case Q.Initialized{s} Initialization{}: True{}
    case Q.Initialized{s} StartWithProof{}: True{}
    case Q.InitialAccepts{} StartWithProof{}: True{}
    case Q.Published{s} Publication{}: True{}
    case Q.Completed{r, s, f} Conclusion{}: True{}
    case Q.Delivered{bs} Complete{}: True{}
    case Q.Interrupted{bs} Interrupted{}: True{}
    case _ _: False{}

def of_that_kind(kind: FrameKind, q: Q.Frame) -> Bool:
  classify(q, kind)

def absent(+kind: FrameKind, xs: List<&2, Q.Frame>) -> Bool:
  match xs:
    case Nil{}: True{}
    case Con{q, rest}: Bool.not(of_that_kind(kind, q)) && absent(kind, rest)

law absent_excludes_query:
  for +kind: FrameKind
  for xs: List<&2, Q.Frame>
  for n: Nat
  for +q: Q.Frame
  for h: {absent(kind, xs) == True{} : Bool}
  for target: {of_that_kind(kind, q) == True{} : Bool}
  for query_result: {Q.query(xs, n) == Some{q} : Maybe<&2, Q.Frame>}
  Empty
def absent_excludes_query(kind, xs, n, q, h, target, query_result):
  match xs n:
    case Nil{} _:
      F.none_negative_some(Q.Frame, q, query_result)
    case Con{+a, t} 0n:
      F.false_negative_true(Equal.trans(Bool, False{}, of_that_kind(kind, a), True{},
        Equal.sym(Bool, of_that_kind(kind, a), False{}, F.negation_true(of_that_kind(kind, a),
          F.and_boolean_left(Bool.not(of_that_kind(kind, a)), absent(kind, t), h))),
        Equal.trans(Bool, of_that_kind(kind, a), of_that_kind(kind, q), True{},
          Equal.cong(Q.Frame, Bool, x => of_that_kind(kind, x), a, q,
            F.some_injective(Q.Frame, a, q, query_result)), target)))
    case Con{a, t} 1n+k:
      absent_excludes_query(kind, t, k, q,
        F.and_boolean_right(Bool.not(of_that_kind(kind, a)), absent(kind, t), h), target, query_result)

law later_delivery_without_macros:
  for kind: FrameKind
  for closes: Bool
  for -s: D.State
  for next: Bool
  {absent(kind, H.later_delivery(closes, s, next)) == True{} : Bool}
def later_delivery_without_macros(kind, closes, s, next):
  match closes next:
    case True{} _: {==}
    case False{} True{}: {==}
    case False{} False{}: {==}

law delivery_without_publication:
  for -s: D.State
  for -bs: List<&2, U32>
  for closes: Bool
  for delivery: H.Delivery
  {absent(Publication{}, H.render_delivery(s, bs, closes, delivery)) == True{} : Bool}
def delivery_without_publication(s, bs, closes, delivery):
  match delivery:
    case H.Complete{next}: later_delivery_without_macros(Publication{}, closes, s, next)
    case H.Broken{prefix}: {==}
    case H.PendingDelivery{}: {==}

law delivery_without_conclusion:
  for -s: D.State
  for -bs: List<&2, U32>
  for closes: Bool
  for delivery: H.Delivery
  {absent(Conclusion{}, H.render_delivery(s, bs, closes, delivery)) == True{} : Bool}
def delivery_without_conclusion(s, bs, closes, delivery):
  match delivery:
    case H.Complete{next}: later_delivery_without_macros(Conclusion{}, closes, s, next)
    case H.Broken{prefix}: {==}
    case H.PendingDelivery{}: {==}

law delivery_broken_never_complete:
  for -s: D.State
  for -bs: List<&2, U32>
  for -closes: Bool
  for -prefix: List<&2, U32>
  {absent(Complete{}, H.render_delivery(s, bs, closes, H.Broken{prefix})) == True{} : Bool}
def delivery_broken_never_complete(s, bs, closes, prefix): {==}

law delivery_complete_never_broken:
  for -s: D.State
  for -bs: List<&2, U32>
  for closes: Bool
  for next: Bool
  {absent(Interrupted{}, H.render_delivery(s, bs, closes, H.Complete{next})) == True{} : Bool}
def delivery_complete_never_broken(s, bs, closes, next):
  later_delivery_without_macros(Interrupted{}, closes, s, next)


def state_publication(q: Q.Frame) -> Maybe<&2, D.State>:
  match q:
    case Q.Published{s}: Some{s}
    case _: None{}

def published_equal(+a: D.State, -b: D.State,
  h: {Some{Q.Published{a}} == Some{Q.Published{b}} : Maybe<&2, Q.Frame>}) -> {b == a : D.State}:
  Equal.sym(D.State, a, b, F.some_injective(D.State, a, b,
    Equal.cong(Q.Frame, Maybe<&2, D.State>, state_publication, Q.Published{a}, Q.Published{b},
      F.some_injective(Q.Frame, Q.Published{a}, Q.Published{b}, h))))

def success_publish_one_time(+s: D.State, +v: D.Value, +bs: List<&2, U32>,
  +closes: Bool, +delivery: H.Delivery, n: Nat, +w: D.State,
  query_result: {Q.query(H.render_conclusion(N.Conclusion{s, S.Response{S.Success{}, v}, bs}, closes, delivery), n) ==
    Some{Q.Published{w}} : Maybe<&2, Q.Frame>}) -> L.E<{n == 1n : Nat}, {w == s : D.State}>:
  match n:
    case 0n:
      L.ex_false(L.E<{0n == 1n : Nat}, {w == s : D.State}>,
        absent_excludes_query(Publication{}, [Q.Prepared{S.Response{S.Success{}, v}, bs}], 0n,
          Q.Published{w}, {==}, {==}, query_result))
    case 1n+k:
      match k:
        case 0n: L.Both{{==}, published_equal(s, w, query_result)}
        case 1n+j:
          match j:
            case 0n:
              L.ex_false(L.E<{2n == 1n : Nat}, {w == s : D.State}>,
                absent_excludes_query(Publication{}, [Q.Completed{S.Response{S.Success{}, v}, s, closes}], 0n,
                  Q.Published{w}, {==}, {==}, query_result))
            case 1n+z:
              L.ex_false(L.E<{3n+z == 1n : Nat}, {w == s : D.State}>,
                absent_excludes_query(Publication{}, H.render_delivery(s, bs, closes, delivery), z,
                  Q.Published{w}, delivery_without_publication(s, bs, closes, delivery), {==}, query_result))

def response_negative_publish(+s: D.State, +r: S.Response, +bs: List<&2, U32>,
  +closes: Bool, +delivery: H.Delivery,
  h: {U.status_success(r) == False{} : Bool}) ->
  {absent(Publication{}, H.render_conclusion(N.Conclusion{s, r, bs}, closes, delivery)) == True{} : Bool}:
  match r:
    case S.Response{S.Success{}, v}:
      F.absurd_boolean(
        {absent(Publication{}, H.render_conclusion(N.Conclusion{s, S.Response{S.Success{}, v}, bs}, closes, delivery)) == True{} : Bool},
        Equal.sym(Bool, True{}, False{}, h))
    case S.Response{S.Refusal{}, v}: delivery_without_publication(s, bs, closes, delivery)
    case S.Response{S.Input{}, v}: delivery_without_publication(s, bs, closes, delivery)
    case S.Response{S.Authentication{}, v}: delivery_without_publication(s, bs, closes, delivery)
    case S.Response{S.Certificate{}, v}: delivery_without_publication(s, bs, closes, delivery)
    case S.Response{S.DataError{}, v}: delivery_without_publication(s, bs, closes, delivery)
    case S.Response{S.Limit{}, v}: delivery_without_publication(s, bs, closes, delivery)
    case S.Response{S.Failure{}, v}: delivery_without_publication(s, bs, closes, delivery)

def negative_exists_publication(+s: D.State, +r: S.Response, +bs: List<&2, U32>, +closes: Bool, +delivery: H.Delivery,
  n: Nat, +w: D.State, without: {U.status_success(r) == False{} : Bool},
  query_result: {Q.query(H.render_conclusion(N.Conclusion{s, r, bs}, closes, delivery), n) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>}) ->
  L.E<{n == 1n : Nat}, {w == s : D.State}>:
  L.ex_false(L.E<{n == 1n : Nat}, {w == s : D.State}>,
    absent_excludes_query(Publication{}, H.render_conclusion(N.Conclusion{s, r, bs}, closes, delivery), n,
      Q.Published{w}, response_negative_publish(s, r, bs, closes, delivery, without), {==}, query_result))

law publication_in_end_and_unique:
  for +conclusion: N.Conclusion
  for +closes: Bool
  for +delivery: H.Delivery
  for n: Nat
  for +w: D.State
  for query_result: {Q.query(H.render_conclusion(conclusion, closes, delivery), n) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>}
  L.E<{n == 1n : Nat}, {w == U.published(conclusion) : D.State}>
def publication_in_end_and_unique(conclusion, closes, delivery, n, w, query_result):
  match conclusion:
    case N.Conclusion{s, S.Response{S.Success{}, v}, bs}:
      success_publish_one_time(s, v, bs, closes, delivery, n, w, query_result)
    case N.Conclusion{s, S.Response{S.Refusal{}, v}, bs}:
      negative_exists_publication(s, S.Response{S.Refusal{}, v}, bs, closes, delivery, n, w, {==}, query_result)
    case N.Conclusion{s, S.Response{S.Input{}, v}, bs}:
      negative_exists_publication(s, S.Response{S.Input{}, v}, bs, closes, delivery, n, w, {==}, query_result)
    case N.Conclusion{s, S.Response{S.Authentication{}, v}, bs}:
      negative_exists_publication(s, S.Response{S.Authentication{}, v}, bs, closes, delivery, n, w, {==}, query_result)
    case N.Conclusion{s, S.Response{S.Certificate{}, v}, bs}:
      negative_exists_publication(s, S.Response{S.Certificate{}, v}, bs, closes, delivery, n, w, {==}, query_result)
    case N.Conclusion{s, S.Response{S.DataError{}, v}, bs}:
      negative_exists_publication(s, S.Response{S.DataError{}, v}, bs, closes, delivery, n, w, {==}, query_result)
    case N.Conclusion{s, S.Response{S.Limit{}, v}, bs}:
      negative_exists_publication(s, S.Response{S.Limit{}, v}, bs, closes, delivery, n, w, {==}, query_result)
    case N.Conclusion{s, S.Response{S.Failure{}, v}, bs}:
      negative_exists_publication(s, S.Response{S.Failure{}, v}, bs, closes, delivery, n, w, {==}, query_result)

law mark_unique_between_parts_absent:
  for +kind: FrameKind
  for before: List<&2, Q.Frame>
  for +later: List<&2, Q.Frame>
  for +mark: Q.Frame
  for n: Nat
  for +q: Q.Frame
  for without_before: {absent(kind, before) == True{} : Bool}
  for without_later: {absent(kind, later) == True{} : Bool}
  for target: {of_that_kind(kind, q) == True{} : Bool}
  for query_result: {Q.query(Q.concatenate(before, Con{mark, later}), n) == Some{q} : Maybe<&2, Q.Frame>}
  L.E<{n == Q.size(before) : Nat}, {q == mark : Q.Frame}>
def mark_unique_between_parts_absent(kind, before, later, mark, n, q, without_before, without_later, target, query_result):
  match before n:
    case Nil{} 0n:
      L.Both{{==}, Equal.sym(Q.Frame, mark, q, F.some_injective(Q.Frame, mark, q, query_result))}
    case Nil{} 1n+k:
      L.ex_false(L.E<{1n+k == 0n : Nat}, {q == mark : Q.Frame}>,
        absent_excludes_query(kind, later, k, q, without_later, target, query_result))
    case Con{+a, t} 0n:
      L.ex_false(L.E<{0n == Q.size(Con{a, t}) : Nat}, {q == mark : Q.Frame}>,
        absent_excludes_query(kind, [a], 0n, q,
          F.and_boolean_intro(Bool.not(of_that_kind(kind, a)), True{},
            F.and_boolean_left(Bool.not(of_that_kind(kind, a)), absent(kind, t), without_before), {==}), target, query_result))
    case Con{a, +t} 1n+k:
      F.combined_pair(L.E<{1n+k == Q.size(Con{a, t}) : Nat}, {q == mark : Q.Frame}>,
        {k == Q.size(t) : Nat}, {q == mark : Q.Frame},
        mark_unique_between_parts_absent(kind, t, later, mark, k, q,
          F.and_boolean_right(Bool.not(of_that_kind(kind, a)), absent(kind, t), without_before), without_later, target, query_result),
        place => equal => L.Both{Equal.cong(Nat, Nat, x => 1n+x, k, Q.size(t), place), equal})

law publication_negative_concludes:
  for r: S.Response
  for -s: D.State
  {absent(Conclusion{}, H.render_publication(r, s)) == True{} : Bool}
def publication_negative_concludes(r, s):
  match r:
    case S.Response{S.Success{}, v}: {==}
    case S.Response{S.Refusal{}, v}: {==}
    case S.Response{S.Input{}, v}: {==}
    case S.Response{S.Authentication{}, v}: {==}
    case S.Response{S.Certificate{}, v}: {==}
    case S.Response{S.DataError{}, v}: {==}
    case S.Response{S.Limit{}, v}: {==}
    case S.Response{S.Failure{}, v}: {==}

law conclusion_in_end_and_unique:
  for +s: D.State
  for +r: S.Response
  for +bs: List<&2, U32>
  for +closes: Bool
  for +delivery: H.Delivery
  for n: Nat
  for +other: Q.Frame
  for kind: {of_that_kind(Conclusion{}, other) == True{} : Bool}
  for query_result: {Q.query(H.render_conclusion(N.Conclusion{s, r, bs}, closes, delivery), n) == Some{other} : Maybe<&2, Q.Frame>}
  L.E<{n == Q.size(Con{Q.Prepared{r, bs}, H.render_publication(r, s)}) : Nat},
    {other == Q.Completed{r, s, closes} : Q.Frame}>
def conclusion_in_end_and_unique(s, r, bs, closes, delivery, n, other, kind, query_result):
  mark_unique_between_parts_absent(Conclusion{}, Con{Q.Prepared{r, bs}, H.render_publication(r, s)},
    H.render_delivery(s, bs, closes, delivery), Q.Completed{r, s, closes}, n, other,
    publication_negative_concludes(r, s), delivery_without_conclusion(s, bs, closes, delivery), kind, query_result)

law delivery_complete_and_unique:
  for +s: D.State
  for +bs: List<&2, U32>
  for +closes: Bool
  for +next: Bool
  for n: Nat
  for +q: Q.Frame
  for kind: {of_that_kind(Complete{}, q) == True{} : Bool}
  for query_result: {Q.query(H.render_delivery(s, bs, closes, H.Complete{next}), n) == Some{q} : Maybe<&2, Q.Frame>}
  L.E<{n == 0n : Nat}, {q == Q.Delivered{bs} : Q.Frame}>
def delivery_complete_and_unique(s, bs, closes, next, n, q, kind, query_result):
  mark_unique_between_parts_absent(Complete{}, Nil{}, H.later_delivery(closes, s, next), Q.Delivered{bs}, n, q,
    {==}, later_delivery_without_macros(Complete{}, closes, s, next), kind, query_result)

law delivery_interrupted_and_unique:
  for -s: D.State
  for -bs: List<&2, U32>
  for -closes: Bool
  for +prefix: List<&2, U32>
  for n: Nat
  for +q: Q.Frame
  for kind: {of_that_kind(Interrupted{}, q) == True{} : Bool}
  for query_result: {Q.query(H.render_delivery(s, bs, closes, H.Broken{prefix}), n) == Some{q} : Maybe<&2, Q.Frame>}
  L.E<{n == 0n : Nat}, {q == Q.Interrupted{prefix} : Q.Frame}>
def delivery_interrupted_and_unique(s, bs, closes, prefix, n, q, kind, query_result):
  mark_unique_between_parts_absent(Interrupted{}, Nil{}, [Q.Closed{}], Q.Interrupted{prefix}, n, q,
    {==}, {==}, kind, query_result)

law concatenate_absence:
  for +kind: FrameKind
  for xs: List<&2, Q.Frame>
  for +ys: List<&2, Q.Frame>
  for hx: {absent(kind, xs) == True{} : Bool}
  for hy: {absent(kind, ys) == True{} : Bool}
  {absent(kind, Q.concatenate(xs, ys)) == True{} : Bool}
def concatenate_absence(kind, xs, ys, hx, hy):
  match xs:
    case Nil{}: hy
    case Con{+h, +t}:
      F.combined_pair({absent(kind, Q.concatenate(Con{h, t}, ys)) == True{} : Bool},
        {Bool.not(of_that_kind(kind, h)) == True{} : Bool}, {absent(kind, t) == True{} : Bool},
        F.and_boolean_separate(Bool.not(of_that_kind(kind, h)), absent(kind, t), hx),
        head => tail => F.and_boolean_intro(Bool.not(of_that_kind(kind, h)), absent(kind, Q.concatenate(t, ys)),
          head, concatenate_absence(kind, t, ys, tail, hy)))

def internal_negative_macro(-kind: FrameKind, q: Q.Frame, h: {M.internal(q) == True{} : Bool}) ->
  {of_that_kind(kind, q) == False{} : Bool}:
  match q:
    case Q.Encoded{v, bs}: {==}
    case Q.Decoded{bs, v}: {==}
    case Q.Stored{s, bs, a}: {==}
    case Q.Checked{pos, n}: {==}
    case Q.Constructed{pos, n}: {==}
    case Q.Read{a, n, d}: {==}
    case Q.Configured{}: {==}
    case Q.InitialAccepts{}: F.absurd_boolean({of_that_kind(kind, Q.InitialAccepts{}) == False{} : Bool}, h)
    case Q.Initialized{s}: F.absurd_boolean({of_that_kind(kind, Q.Initialized{s}) == False{} : Bool}, h)
    case Q.InitialRefused{s}: F.absurd_boolean({of_that_kind(kind, Q.InitialRefused{s}) == False{} : Bool}, h)
    case Q.Received{r}: {==}
    case Q.Authenticated{r, ctx}: {==}
    case Q.Accepts{r, ctx}: {==}
    case Q.Rejected{r, ctx}: {==}
    case Q.Started{r, ctx}: {==}
    case Q.Evaluated{r, ctx, p}: {==}
    case Q.Operated{e, s, o, r}: {==}
    case Q.Prepared{r, bs}: {==}
    case Q.Published{s}: F.absurd_boolean({of_that_kind(kind, Q.Published{s}) == False{} : Bool}, h)
    case Q.Visible{s}: {==}
    case Q.Failed{stage, id, fatal}: {==}
    case Q.Completed{r, s, f}: F.absurd_boolean({of_that_kind(kind, Q.Completed{r, s, f}) == False{} : Bool}, h)
    case Q.Delivered{bs}: F.absurd_boolean({of_that_kind(kind, Q.Delivered{bs}) == False{} : Bool}, h)
    case Q.Interrupted{bs}: F.absurd_boolean({of_that_kind(kind, Q.Interrupted{bs}) == False{} : Bool}, h)
    case Q.Closed{}: {==}
    case Q.Next{a, b}: {==}
    case Q.Inspection{d}: F.absurd_boolean({of_that_kind(kind, Q.Inspection{d}) == False{} : Bool}, h)
    case Q.Effect{d}: F.absurd_boolean({of_that_kind(kind, Q.Effect{d}) == False{} : Bool}, h)

def internal_without_macros(+kind: FrameKind, xs: List<&2, Q.Frame>, h: M.Internal(xs)) ->
  {absent(kind, xs) == True{} : Bool}:
  match xs h:
    case Nil{} _: {==}
    case Con{+q, +t} L.Both{head, tail}:
      F.and_boolean_intro(Bool.not(of_that_kind(kind, q)), absent(kind, t),
        Equal.cong(Bool, Bool, Bool.not, of_that_kind(kind, q), False{}, internal_negative_macro(kind, q, head)),
        internal_without_macros(kind, t, tail))

law primitive_without_macros:
  for +kind: FrameKind
  for +p: M.Primitive
  {absent(kind, M.expand(p)) == True{} : Bool}
def primitive_without_macros(kind, p):
  internal_without_macros(kind, M.expand(p), M.expand_internal(p))

law primitives_without_macros:
  for +kind: FrameKind
  for +ps: List<&2, M.Primitive>
  {absent(kind, M.expand_primitives(ps)) == True{} : Bool}
def primitives_without_macros(kind, ps):
  internal_without_macros(kind, M.expand_primitives(ps), M.primitives_only_generate_internal(ps))

law execution_without_macros:
  for +kind: FrameKind
  for +r: Protocol.Request
  for +ctx: D.Context
  for xs: List<&2, Q.FrameExec>
  {absent(kind, Q.expand_exec(r, ctx, xs)) == True{} : Bool}
def execution_without_macros(kind, r, ctx, xs):
  match xs:
    case Nil{}: {==}
    case Con{Q.Evaluation{execution_trace}, t}: execution_without_macros(kind, r, ctx, t)
    case Con{Q.Operation{e, s, o, result}, t}: execution_without_macros(kind, r, ctx, t)

def micro_input_without_macros(kind: FrameKind, m: H.Micro) ->
  {absent(kind, H.micro_input(m)) == True{} : Bool}:
  match m:
    case H.Micro{a, b, c, d}: primitives_without_macros(kind, a)

def micro_authentication_without_macros(kind: FrameKind, m: H.Micro) ->
  {absent(kind, H.micro_authentication(m)) == True{} : Bool}:
  match m:
    case H.Micro{a, b, c, d}: primitives_without_macros(kind, b)

def micro_execution_without_macros(kind: FrameKind, m: H.Micro) ->
  {absent(kind, H.micro_execution(m)) == True{} : Bool}:
  match m:
    case H.Micro{a, b, c, d}: primitives_without_macros(kind, c)

def micro_output_without_macros(kind: FrameKind, m: H.Micro) ->
  {absent(kind, H.micro_output(m)) == True{} : Bool}:
  match m:
    case H.Micro{a, b, c, d}: primitives_without_macros(kind, d)

def received_without_macros(+kind: FrameKind, +m: H.Micro, +r: Protocol.Request) ->
  {absent(kind, H.render_received(m, r)) == True{} : Bool}:
  concatenate_absence(kind, H.micro_input(m), [Q.Received{r}], micro_input_without_macros(kind, m), {==})

def authenticated_without_macros(+kind: FrameKind, +m: H.Micro, +r: Protocol.Request, +ctx: D.Context) ->
  {absent(kind, H.render_authenticated(m, r, ctx)) == True{} : Bool}:
  concatenate_absence(kind, H.render_received(m, r), Q.concatenate(H.micro_authentication(m), [Q.Authenticated{r, Some{ctx}}]),
    received_without_macros(kind, m, r),
    concatenate_absence(kind, H.micro_authentication(m), [Q.Authenticated{r, Some{ctx}}], micro_authentication_without_macros(kind, m), {==}))

def verified_without_macros(+kind: FrameKind, +m: H.Micro, +r: Protocol.Request, +ctx: D.Context) ->
  {absent(kind, H.render_verified(m, r, ctx)) == True{} : Bool}:
  concatenate_absence(kind, H.render_authenticated(m, r, ctx), [Q.Accepts{r, ctx}], authenticated_without_macros(kind, m, r, ctx), {==})

def started_without_macros(+kind: FrameKind, +m: H.Micro, +r: Protocol.Request, +ctx: D.Context) ->
  {absent(kind, H.render_started(m, r, ctx)) == True{} : Bool}:
  concatenate_absence(kind, H.render_verified(m, r, ctx), Q.concatenate(H.micro_execution(m), [Q.Started{r, ctx}]),
    verified_without_macros(kind, m, r, ctx),
    concatenate_absence(kind, H.micro_execution(m), [Q.Started{r, ctx}], micro_execution_without_macros(kind, m), {==}))

def execution_host_without_macros(+kind: FrameKind, +m: H.Micro, +r: Protocol.Request, +ctx: D.Context,
  +exec: List<&2, Q.FrameExec>) ->
  {absent(kind, H.render_execution(m, r, ctx, exec)) == True{} : Bool}:
  concatenate_absence(kind, H.render_started(m, r, ctx), Q.expand_exec(r, ctx, exec),
    started_without_macros(kind, m, r, ctx), execution_without_macros(kind, r, ctx, exec))

law phase_previous_without_macros:
  for +kind: FrameKind
  for +m: H.Micro
  for phase: H.PhaseBefore
  {absent(kind, H.render_phase(m, phase)) == True{} : Bool}
def phase_previous_without_macros(kind, m, phase):
  match phase:
    case H.BeforeInput{}: micro_input_without_macros(kind, m)
    case H.AfterReceive{r}: received_without_macros(kind, m, r)
    case H.AfterAuthenticate{r, ctx}: authenticated_without_macros(kind, m, r, ctx)
    case H.AfterVerify{r, ctx}: verified_without_macros(kind, m, r, ctx)
    case H.Executing{r, ctx, exec}: execution_host_without_macros(kind, m, r, ctx, exec)
    case H.AfterPrepare{+r, +ctx, +exec, N.Prepared{w, ts, +rp, +bs}}:
      concatenate_absence(kind, H.render_execution(m, r, ctx, exec),
        Q.concatenate(H.micro_output(m), [Q.Prepared{rp, bs}]),
        execution_host_without_macros(kind, m, r, ctx, exec),
        concatenate_absence(kind, H.micro_output(m), [Q.Prepared{rp, bs}], micro_output_without_macros(kind, m), {==}))

law shift_preserves_before:
  for prefix: Nat
  for -a: Nat
  for -b: Nat
  for less: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_lt(Nat.add(prefix, a), Nat.add(prefix, b)) == True{} : Bool}
def shift_preserves_before(prefix, a, b, less):
  match prefix:
    case 0n: less
    case 1n+k: shift_preserves_before(k, a, b, less)

law preparation_before_of_publication_in_end:
  for +conclusion: N.Conclusion
  for +closes: Bool
  for +delivery: H.Delivery
  for n: Nat
  for +w: D.State
  for query_result: {Q.query(H.render_conclusion(conclusion, closes, delivery), n) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>}
  exs r: S.Response
  exs bs: List<&2, U32>
  exs u: Nat
  L.E<{Nat.is_lt(u, n) == True{} : Bool},
    {Q.query(H.render_conclusion(conclusion, closes, delivery), u) == Some{Q.Prepared{r, bs}} : Maybe<&2, Q.Frame>}>
def preparation_before_of_publication_in_end(conclusion, closes, delivery, n, w, query_result):
  match conclusion:
    case N.Conclusion{+s, +r, +bs}:
      F.combined_pair(
        (&r0: S.Response -> &bytes: List<&2, U32> -> &u: Nat ->
          L.E<{Nat.is_lt(u, n) == True{} : Bool},
            {Q.query(H.render_conclusion(N.Conclusion{s, r, bs}, closes, delivery), u) == Some{Q.Prepared{r0, bytes}} : Maybe<&2, Q.Frame>}>),
        {n == 1n : Nat}, {w == s : D.State},
        publication_in_end_and_unique(N.Conclusion{s, r, bs}, closes, delivery, n, w, query_result),
        place => state =>
          (r, bs, 0n, L.Both{
            (%Equal.sym(Nat, n, 1n, place) : {Nat.is_lt(0n, _) == True{} : Bool} {==}), {==}}))

# Operational origin of visibility: no database invariant is assumed.
def WithoutPublicationBefore(-xs: List<&2, Q.Frame>, -t: Nat) -> Type:
  @u: Nat -> @w: D.State -> {Nat.is_lt(u, t) == True{} : Bool} ->
    {Q.query(xs, u) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>} -> Empty

def Origin(-xs: List<&2, Q.Frame>, -t: Nat, -initial: D.State, -visible: D.State) -> Type:
  L.Disjunction<L.E<{visible == initial : D.State}, WithoutPublicationBefore(xs, t)>,
    (&u: Nat -> L.E<{Nat.is_lt(u, t) == True{} : Bool},
      {Q.query(xs, u) == Some{Q.Published{visible}} : Maybe<&2, Q.Frame>}>)>

def never_before_zero(u: Nat, less: {Nat.is_lt(u, 0n) == True{} : Bool}) -> Empty:
  match u:
    case 0n: F.false_negative_true(less)
    case 1n+k: F.false_negative_true(less)

def before_zero(-xs: List<&2, Q.Frame>) -> WithoutPublicationBefore(xs, 0n):
  u => w => less => query_result => never_before_zero(u, less)

def before_empty(-t: Nat) -> WithoutPublicationBefore(Nil{}, t):
  u => w => less => query_result => F.none_negative_some(Q.Frame, Q.Published{w}, query_result)

def absence_front(u: Nat, +q: Q.Frame, +xs: List<&2, Q.Frame>, +t: Nat,
  negative: {of_that_kind(Publication{}, q) == False{} : Bool}, rest: WithoutPublicationBefore(xs, t), +w: D.State,
  less: {Nat.is_lt(u, 1n+t) == True{} : Bool},
  query_result: {Q.query(Con{q, xs}, u) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>}) -> Empty:
  match u:
    case 0n:
      F.false_negative_true(Equal.trans(Bool, False{}, of_that_kind(Publication{}, q), True{},
        Equal.sym(Bool, of_that_kind(Publication{}, q), False{}, negative),
        Equal.cong(Q.Frame, Bool, x => of_that_kind(Publication{}, x), q, Q.Published{w},
          F.some_injective(Q.Frame, q, Q.Published{w}, query_result))))
    case 1n+v: rest(v, w, less, query_result)

def extend_absence(+q: Q.Frame, +xs: List<&2, Q.Frame>, +t: Nat,
  negative: {of_that_kind(Publication{}, q) == False{} : Bool}, rest: WithoutPublicationBefore(xs, t)) ->
  WithoutPublicationBefore(Con{q, xs}, 1n+t):
  u => w => less => query_result => absence_front(u, q, xs, t, negative, rest, w, less, query_result)

# The origin also records initialization; the fold remains the computed state.
def OriginGeneral(-xs: List<&2, Q.Frame>, -t: Nat,
  -initial: Maybe<&2, D.State>, -visible: D.State) -> Type:
  L.Disjunction<L.E<{initial == Some{visible} : Maybe<&2, D.State>}, WithoutPublicationBefore(xs, t)>,
    L.Disjunction<(&u: Nat -> L.E<{Nat.is_lt(u, t) == True{} : Bool},
      {Q.query(xs, u) == Some{Q.Published{visible}} : Maybe<&2, Q.Frame>}>),
      (&u: Nat -> L.E<{Nat.is_lt(u, t) == True{} : Bool},
        {Q.query(xs, u) == Some{Q.Initialized{visible}} : Maybe<&2, Q.Frame>}>)>>

def extend_origin(+q: Q.Frame, +xs: List<&2, Q.Frame>, +t: Nat,
  -initial: Maybe<&2, D.State>, +visible: D.State,
  negative: {of_that_kind(Publication{}, q) == False{} : Bool}, origin: OriginGeneral(xs, t, initial, visible)) ->
  OriginGeneral(Con{q, xs}, 1n+t, initial, visible):
  match origin:
    case L.Left{L.Both{equal, none}}:
      L.Left{L.Both{equal, extend_absence(q, xs, t, negative, none)}}
    case L.Right{L.Left{(u, L.Both{less, query_result})}}:
      L.Right{L.Left{(1n+u, L.Both{less, query_result})}}
    case L.Right{L.Right{(u, L.Both{less, query_result})}}:
      L.Right{L.Right{(1n+u, L.Both{less, query_result})}}

def origin_published(+xs: List<&2, Q.Frame>, +t: Nat, -initial: Maybe<&2, D.State>,
  +published: D.State, +visible: D.State, origin: OriginGeneral(xs, t, Some{published}, visible)) ->
  OriginGeneral(Con{Q.Published{published}, xs}, 1n+t, initial, visible):
  match origin:
    case L.Left{L.Both{equal, none}}:
      L.Right{L.Left{(0n, L.Both{{==}, Equal.cong(D.State, Maybe<&2, Q.Frame>, w => Some{Q.Published{w}},
        published, visible, F.some_injective(D.State, published, visible, equal))})}}
    case L.Right{L.Left{(u, L.Both{less, query_result})}}:
      L.Right{L.Left{(1n+u, L.Both{less, query_result})}}
    case L.Right{L.Right{(u, L.Both{less, query_result})}}:
      L.Right{L.Right{(1n+u, L.Both{less, query_result})}}

def origin_started(+xs: List<&2, Q.Frame>, +t: Nat, -initial: Maybe<&2, D.State>,
  +seed: D.State, +visible: D.State, origin: OriginGeneral(xs, t, Some{seed}, visible)) ->
  OriginGeneral(Con{Q.Initialized{seed}, xs}, 1n+t, initial, visible):
  match origin:
    case L.Left{L.Both{equal, none}}:
      L.Right{L.Right{(0n, L.Both{{==}, Equal.cong(D.State, Maybe<&2, Q.Frame>, w => Some{Q.Initialized{w}},
        seed, visible, F.some_injective(D.State, seed, visible, equal))})}}
    case L.Right{L.Left{(u, L.Both{less, query_result})}}:
      L.Right{L.Left{(1n+u, L.Both{less, query_result})}}
    case L.Right{L.Right{(u, L.Both{less, query_result})}}:
      L.Right{L.Right{(1n+u, L.Both{less, query_result})}}

law origin_general_of_state_visible:
  for t: Nat
  for +xs: List<&2, Q.Frame>
  for +initial: Maybe<&2, D.State>
  for +visible: D.State
  for seen: {Q.state_in(xs, t, initial) == Some{visible} : Maybe<&2, D.State>}
  OriginGeneral(xs, t, initial, visible)
def origin_general_of_state_visible(t, xs, initial, visible, seen):
  match t:
    case 0n:
      L.Left{L.Both{
        Equal.trans(Maybe<&2, D.State>, initial, Q.state_in(xs, 0n, initial), Some{visible},
          Equal.sym(Maybe<&2, D.State>, Q.state_in(xs, 0n, initial), initial,
            Q.state_before_of_first_step(xs, initial)), seen), before_zero(xs)}}
    case 1n+ +k:
      match xs:
        case Nil{}: L.Left{L.Both{seen, before_empty(1n+k)}}
        case Con{q, +rest}:
          match q:
            case Q.Published{+w}:
              origin_published(rest, k, initial, w, visible, origin_general_of_state_visible(k, rest, Some{w}, visible, seen))
            case Q.Initialized{+w}:
              origin_started(rest, k, initial, w, visible, origin_general_of_state_visible(k, rest, Some{w}, visible, seen))
            case Q.Configured{}:
              extend_origin(Q.Configured{}, rest, k, initial, visible, {==},
                origin_general_of_state_visible(k, rest, initial, visible, seen))
            case Q.InitialAccepts{}:
              extend_origin(Q.InitialAccepts{}, rest, k, initial, visible, {==},
                origin_general_of_state_visible(k, rest, initial, visible, seen))
            case Q.InitialRefused{+status}:
              extend_origin(Q.InitialRefused{status}, rest, k, initial, visible, {==},
                origin_general_of_state_visible(k, rest, initial, visible, seen))
            case Q.Encoded{+v, +bs}:
              extend_origin(Q.Encoded{v, bs}, rest, k, initial, visible, {==},
                origin_general_of_state_visible(k, rest, initial, visible, seen))
            case Q.Decoded{+bs, +v}:
              extend_origin(Q.Decoded{bs, v}, rest, k, initial, visible, {==},
                origin_general_of_state_visible(k, rest, initial, visible, seen))
            case Q.Stored{+s, +bs, +a}:
              extend_origin(Q.Stored{s, bs, a}, rest, k, initial, visible, {==},
                origin_general_of_state_visible(k, rest, initial, visible, seen))
            case Q.Checked{+p, +n}:
              extend_origin(Q.Checked{p, n}, rest, k, initial, visible, {==},
                origin_general_of_state_visible(k, rest, initial, visible, seen))
            case Q.Constructed{+p, +n}:
              extend_origin(Q.Constructed{p, n}, rest, k, initial, visible, {==},
                origin_general_of_state_visible(k, rest, initial, visible, seen))
            case Q.Read{+a, +n, +d}:
              extend_origin(Q.Read{a, n, d}, rest, k, initial, visible, {==},
                origin_general_of_state_visible(k, rest, initial, visible, seen))
            case Q.Received{+r}:
              extend_origin(Q.Received{r}, rest, k, initial, visible, {==},
                origin_general_of_state_visible(k, rest, initial, visible, seen))
            case Q.Authenticated{+r, +ctx}:
              extend_origin(Q.Authenticated{r, ctx}, rest, k, initial, visible, {==},
                origin_general_of_state_visible(k, rest, initial, visible, seen))
            case Q.Accepts{+r, +ctx}:
              extend_origin(Q.Accepts{r, ctx}, rest, k, initial, visible, {==},
                origin_general_of_state_visible(k, rest, initial, visible, seen))
            case Q.Rejected{+r, +ctx}:
              extend_origin(Q.Rejected{r, ctx}, rest, k, initial, visible, {==},
                origin_general_of_state_visible(k, rest, initial, visible, seen))
            case Q.Started{+r, +ctx}:
              extend_origin(Q.Started{r, ctx}, rest, k, initial, visible, {==},
                origin_general_of_state_visible(k, rest, initial, visible, seen))
            case Q.Evaluated{+r, +ctx, +execution_trace}:
              extend_origin(Q.Evaluated{r, ctx, execution_trace}, rest, k, initial, visible, {==},
                origin_general_of_state_visible(k, rest, initial, visible, seen))
            case Q.Operated{+e, +s, +o, +r}:
              extend_origin(Q.Operated{e, s, o, r}, rest, k, initial, visible, {==},
                origin_general_of_state_visible(k, rest, initial, visible, seen))
            case Q.Prepared{+r, +bs}:
              extend_origin(Q.Prepared{r, bs}, rest, k, initial, visible, {==},
                origin_general_of_state_visible(k, rest, initial, visible, seen))
            case Q.Visible{+s}:
              extend_origin(Q.Visible{s}, rest, k, initial, visible, {==},
                origin_general_of_state_visible(k, rest, initial, visible, seen))
            case Q.Failed{+stage, +id, +fatal}:
              extend_origin(Q.Failed{stage, id, fatal}, rest, k, initial, visible, {==},
                origin_general_of_state_visible(k, rest, initial, visible, seen))
            case Q.Completed{+r, +s, +closes}:
              extend_origin(Q.Completed{r, s, closes}, rest, k, initial, visible, {==},
                origin_general_of_state_visible(k, rest, initial, visible, seen))
            case Q.Delivered{+bs}:
              extend_origin(Q.Delivered{bs}, rest, k, initial, visible, {==},
                origin_general_of_state_visible(k, rest, initial, visible, seen))
            case Q.Interrupted{+bs}:
              extend_origin(Q.Interrupted{bs}, rest, k, initial, visible, {==},
                origin_general_of_state_visible(k, rest, initial, visible, seen))
            case Q.Closed{}:
              extend_origin(Q.Closed{}, rest, k, initial, visible, {==},
                origin_general_of_state_visible(k, rest, initial, visible, seen))
            case Q.Next{+a, +b}:
              extend_origin(Q.Next{a, b}, rest, k, initial, visible, {==},
                origin_general_of_state_visible(k, rest, initial, visible, seen))
            case Q.Inspection{+d}:
              extend_origin(Q.Inspection{d}, rest, k, initial, visible, {==},
                origin_general_of_state_visible(k, rest, initial, visible, seen))
            case Q.Effect{+d}:
              extend_origin(Q.Effect{d}, rest, k, initial, visible, {==},
                origin_general_of_state_visible(k, rest, initial, visible, seen))

def origin_without_restart(+xs: List<&2, Q.Frame>, +t: Nat, +initial: D.State, +visible: D.State,
  without_start: {absent(Initialization{}, xs) == True{} : Bool}, origin: OriginGeneral(xs, t, Some{initial}, visible)) ->
  Origin(xs, t, initial, visible):
  match origin:
    case L.Left{L.Both{equal, none}}:
      L.Left{L.Both{Equal.sym(D.State, initial, visible, F.some_injective(D.State, initial, visible, equal)), none}}
    case L.Right{L.Left{occurrence}}: L.Right{occurrence}
    case L.Right{L.Right{(u, L.Both{less, query_result})}}:
      L.ex_false(Origin(xs, t, initial, visible),
        absent_excludes_query(Initialization{}, xs, u, Q.Initialized{visible}, without_start, {==}, query_result))

law origin_of_state_visible:
  for +t: Nat
  for +xs: List<&2, Q.Frame>
  for +initial: D.State
  for +visible: D.State
  for without_start: {absent(Initialization{}, xs) == True{} : Bool}
  for seen: {Q.state_in(xs, t, Some{initial}) == Some{visible} : Maybe<&2, D.State>}
  Origin(xs, t, initial, visible)
def origin_of_state_visible(t, xs, initial, visible, without_start, seen):
  origin_without_restart(xs, t, initial, visible, without_start, origin_general_of_state_visible(t, xs, Some{initial}, visible, seen))

# Generated initialization only installs the seed, after its actual encoding.
def state_started(q: Q.Frame) -> Maybe<&2, D.State>:
  match q:
    case Q.Initialized{s}: Some{s}
    case _: None{}

def started_equal(+a: D.State, -b: D.State,
  h: {Some{Q.Initialized{a}} == Some{Q.Initialized{b}} : Maybe<&2, Q.Frame>}) -> {b == a : D.State}:
  Equal.sym(D.State, a, b, F.some_injective(D.State, a, b,
    Equal.cong(Q.Frame, Maybe<&2, D.State>, state_started, Q.Initialized{a}, Q.Initialized{b},
      F.some_injective(Q.Frame, Q.Initialized{a}, Q.Initialized{b}, h))))

def initial_without_publication(result: Maybe<&2, List<&2, U32>>, -s: D.State) ->
  {absent(Publication{}, H.render_initial(result, s)) == True{} : Bool}:
  match result:
    case None{}: {==}
    case Some{bs}: {==}

def initial_only_starts_seed(+result: Maybe<&2, List<&2, U32>>, +s: D.State, n: Nat, +w: D.State,
  h: {Q.query(H.render_initial(result, s), n) == Some{Q.Initialized{w}} : Maybe<&2, Q.Frame>}) ->
  {w == s : D.State}:
  match result:
    case None{}:
      L.ex_false({w == s : D.State}, absent_excludes_query(Initialization{}, H.render_initial(None{}, s), n,
        Q.Initialized{w}, {==}, {==}, h))
    case Some{+bs}:
      match n:
        case 0n:
          L.ex_false({w == s : D.State}, absent_excludes_query(Initialization{},
            [Q.Encoded{D.state_value(s), Some{bs}}], 0n, Q.Initialized{w}, {==}, {==}, h))
        case 1n+k:
          match k:
            case 0n:
              L.ex_false({w == s : D.State}, absent_excludes_query(Initialization{},
                [Q.Stored{s, bs, s}], 0n, Q.Initialized{w}, {==}, {==}, h))
            case 1n+j:
              match j:
                case 0n: started_equal(s, w, h)
                case 1n+z: L.ex_false({w == s : D.State}, F.none_negative_some(Q.Frame, Q.Initialized{w}, h))

law remove_prefix_absent:
  for +kind: FrameKind
  for before: List<&2, Q.Frame>
  for +later: List<&2, Q.Frame>
  for n: Nat
  for +q: Q.Frame
  for without: {absent(kind, before) == True{} : Bool}
  for target: {of_that_kind(kind, q) == True{} : Bool}
  for obtained: {Q.query(Q.concatenate(before, later), n) == Some{q} : Maybe<&2, Q.Frame>}
  exs u: Nat
  {Q.query(later, u) == Some{q} : Maybe<&2, Q.Frame>}
def remove_prefix_absent(kind, before, later, n, q, without, target, obtained):
  match before n:
    case Nil{} _: (n, obtained)
    case Con{+a, t} 0n:
      L.ex_false((&u: Nat -> {Q.query(later, u) == Some{q} : Maybe<&2, Q.Frame>}),
        absent_excludes_query(kind, [a], 0n, q,
          F.and_boolean_intro(Bool.not(of_that_kind(kind, a)), True{},
            F.and_boolean_left(Bool.not(of_that_kind(kind, a)), absent(kind, t), without), {==}), target, obtained))
    case Con{a, t} 1n+k:
      remove_prefix_absent(kind, t, later, k, q,
        F.and_boolean_right(Bool.not(of_that_kind(kind, a)), absent(kind, t), without), target, obtained)

def initialization_without_publication(+m: H.Micro, +s: D.State) ->
  {absent(Publication{}, H.render(m, s, H.InitialOk{})) == True{} : Bool}:
  concatenate_absence(Publication{}, H.micro_output(m), H.render_initial(Protocol.encode(D.state_value(s)), s),
    micro_output_without_macros(Publication{}, m), initial_without_publication(Protocol.encode(D.state_value(s)), s))

def suffix_starts_seed(+result: Maybe<&2, List<&2, U32>>, +s: D.State, +w: D.State,
  h: &u: Nat -> {Q.query(H.render_initial(result, s), u) == Some{Q.Initialized{w}} : Maybe<&2, Q.Frame>}) ->
  {w == s : D.State}:
  match h:
    case (u, query_result): initial_only_starts_seed(result, s, u, w, query_result)

def prefix_starts_seed(+m: H.Micro, +s: D.State, +w: D.State,
  h: &u: Nat -> {Q.query(Q.concatenate(H.micro_output(m), H.render_initial(Protocol.encode(D.state_value(s)), s)), u) ==
    Some{Q.Initialized{w}} : Maybe<&2, Q.Frame>}) -> {w == s : D.State}:
  match h:
    case (u, query_result):
      suffix_starts_seed(Protocol.encode(D.state_value(s)), s, w,
        remove_prefix_absent(Initialization{}, H.micro_output(m), H.render_initial(Protocol.encode(D.state_value(s)), s),
          u, Q.Initialized{w}, micro_output_without_macros(Initialization{}, m), {==}, query_result))

def initialization_only_starts_seed(+m: H.Micro, +s: D.State, t: Nat, +w: D.State,
  h: {Q.query(H.render(m, s, H.InitialOk{}), t) == Some{Q.Initialized{w}} : Maybe<&2, Q.Frame>}) ->
  {w == s : D.State}:
  prefix_starts_seed(m, s, w, remove_prefix_absent(Initialization{}, [Q.Configured{}, Q.InitialAccepts{}],
    Q.concatenate(H.micro_output(m), H.render_initial(Protocol.encode(D.state_value(s)), s)), t, Q.Initialized{w}, {==}, {==}, h))

def origin_initialization(+t: Nat, +m: H.Micro, +s: D.State, +w: D.State,
  origin: OriginGeneral(H.render(m, s, H.InitialOk{}), t, None{}, w)) -> Origin(H.render(m, s, H.InitialOk{}), t, s, w):
  match origin:
    case L.Left{L.Both{equal, none}}:
      L.ex_false(Origin(H.render(m, s, H.InitialOk{}), t, s, w), F.none_negative_some(D.State, w, equal))
    case L.Right{L.Left{(u, L.Both{less, query_result})}}:
      L.ex_false(Origin(H.render(m, s, H.InitialOk{}), t, s, w),
        absent_excludes_query(Publication{}, H.render(m, s, H.InitialOk{}), u, Q.Published{w}, initialization_without_publication(m, s), {==}, query_result))
    case L.Right{L.Right{(u, L.Both{less, query_result})}}:
      L.Left{L.Both{initialization_only_starts_seed(m, s, u, w, query_result),
        v => s2 => previous => published => absent_excludes_query(Publication{}, H.render(m, s, H.InitialOk{}), v,
          Q.Published{s2}, initialization_without_publication(m, s), {==}, published)}}

law origin_of_state_initialized:
  for +t: Nat
  for +m: H.Micro
  for +s: D.State
  for +w: D.State
  for seen: {Q.state_in(H.render(m, s, H.InitialOk{}), t, None{}) == Some{w} : Maybe<&2, D.State>}
  Origin(H.render(m, s, H.InitialOk{}), t, s, w)
def origin_of_state_initialized(t, m, s, w, seen):
  origin_initialization(t, m, s, w, origin_general_of_state_visible(t, H.render(m, s, H.InitialOk{}), None{}, w, seen))

# Representation lifting: both maps eliminate/introduce queries of
# the SAME closed source, not hypotheses about Law6.
def contradict_publication_previous(-a: I.Environment, -k: String, -x: I.Scenario,
  -xs: List<&2, Q.Frame>, -t: Nat, without: WithoutPublicationBefore(xs, t),
  extract: @u: Nat -> @s: D.State -> I.Happens(a, k, x, u, I.Published{s}) ->
    {Q.query(xs, u) == Some{Q.Published{s}} : Maybe<&2, Q.Frame>},
  +s: D.State, previous: I.Before(a, k, x, t, I.Published{s})) -> Empty:
  match previous:
    case (+u, L.Both{order, fact}): without(u, s, order, extract(u, s, fact))

law origin_for_rule6:
  for -a: I.Environment
  for -k: String
  for -x: I.Scenario
  for -t: Nat
  for -xs: List<&2, Q.Frame>
  for +s: D.State
  for origin: Origin(xs, t, I.initial(x), s)
  for introduce: @u: Nat -> @w: D.State ->
    {Q.query(xs, u) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>} -> I.Happens(a, k, x, u, I.Published{w})
  for extract: @u: Nat -> @w: D.State -> I.Happens(a, k, x, u, I.Published{w}) ->
    {Q.query(xs, u) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>}
  K.Rule6(I.StateVisible{s}, a, k, x, t)
def origin_for_rule6(a, k, x, t, xs, s, origin, introduce, extract):
  match origin:
    case L.Left{L.Both{equal, none}}:
      L.Left{L.Both{equal, w => previous => contradict_publication_previous(a, k, x, xs, t, none, extract, w, previous)}}
    case L.Right{(+u, L.Both{order, query_result})}:
      L.Right{(u, L.Both{order, introduce(u, s, query_result)})}

# Preparation content follows from the actual function; the response cause
# is still proved separately in the execution/error branch that produced it.
def DataPrepared(-c: S.Configuration, -p: N.Prepared) -> Type:
  L.E<I.ErrorFixed(U.response(p)),
    L.E<Protocol.Message(S.response_value(U.response(p)), Preparation.bytes_prepared(p)),
      {R.fits(R.limit_response(S.limits(c)), S.response_value(U.response(p))) == True{} : Bool}>>

def join_preparation(-c: S.Configuration, -w: D.State, -ts: List<&2, S.OperationEvent>,
  -r: S.Response, -bs: List<&2, U32>, payload: Preparation.Preparable(S.limits(c), r),
  message: Protocol.Message(S.response_value(r), bs)) -> DataPrepared(c, N.Prepared{w, ts, r, bs}):
  match payload:
    case L.Both{value, size}: L.Both{value, L.Both{message, size}}

def data_of_preparation(~c: S.Configuration, +w: D.State, +ts: List<&2, S.OperationEvent>,
  +proposal: S.Response, +p: N.Prepared,
  faithful: Preparation.Faithful(w, ts, R.finalize(proposal, c, w), p),
  limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool}) -> DataPrepared(c, p):
  match faithful:
    case L.Both{equal, message}:
      %Equal.sym(N.Prepared, p, N.Prepared{w, ts, R.finalize(proposal, c, w), Preparation.bytes_prepared(p)}, equal) : DataPrepared(c, _)
      join_preparation(c, w, ts, R.finalize(proposal, c, w), Preparation.bytes_prepared(p),
        Preparation.finalize_guarantees_payload_and_size(proposal, c, w, limits), message)

law prepare_real_guarantees_payload_message_and_size:
  for ~c: S.Configuration
  for +w: D.State
  for +ts: List<&2, S.OperationEvent>
  for +proposal: S.Response
  for +p: N.Prepared
  for obtained: {N.prepare(N.Stopped{w, ts, proposal}, c) == Some{p} : Maybe<&2, N.Prepared>}
  for limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool}
  DataPrepared(c, p)
def prepare_real_guarantees_payload_message_and_size(c, w, ts, proposal, p, obtained, limits):
  data_of_preparation(c, w, ts, proposal, p,
    Preparation.prepare_preserves_response_state_events_and_bytes(N.Stopped{w, ts, proposal}, c, p, obtained), limits)

# Locates milestones in the suffix; Micro/execution generates the prefix.
def part_after_prefix(+kind: FrameKind, +before: List<&2, Q.Frame>, -later: List<&2, Q.Frame>,
  -t: Nat, +q: Q.Frame, without: {absent(kind, before) == True{} : Bool},
  target: {of_that_kind(kind, q) == True{} : Bool}, part: Q.Part(before, later, t, q)) ->
  &u: Nat -> L.E<{t == Nat.add(Q.size(before), u) : Nat},
    {Q.query(later, u) == Some{q} : Maybe<&2, Q.Frame>}>:
  match part:
    case L.Left{(u, L.Both{pos, query_result})}:
      L.ex_false((&u: Nat -> L.E<{t == Nat.add(Q.size(before), u) : Nat},
        {Q.query(later, u) == Some{q} : Maybe<&2, Q.Frame>}>),
        absent_excludes_query(kind, before, u, q, without, target, query_result))
    case L.Right{occurrence}: occurrence

def locate_in_suffix(+kind: FrameKind, +before: List<&2, Q.Frame>, -later: List<&2, Q.Frame>,
  +t: Nat, +q: Q.Frame, without: {absent(kind, before) == True{} : Bool},
  target: {of_that_kind(kind, q) == True{} : Bool},
  query_result: {Q.query(Q.concatenate(before, later), t) == Some{q} : Maybe<&2, Q.Frame>}) ->
  &u: Nat -> L.E<{t == Nat.add(Q.size(before), u) : Nat},
    {Q.query(later, u) == Some{q} : Maybe<&2, Q.Frame>}>:
  part_after_prefix(kind, before, later, t, q, without, target, Q.divide_query(before, later, t, q, query_result))

def publication_located(+before: List<&2, Q.Frame>, +conclusion: N.Conclusion, +closes: Bool, +delivery: H.Delivery,
  -t: Nat, +w: D.State, part: &u: Nat -> L.E<{t == Nat.add(Q.size(before), u) : Nat},
    {Q.query(H.render_conclusion(conclusion, closes, delivery), u) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>}>) ->
  L.E<{t == Nat.add(Q.size(before), 1n) : Nat}, {w == U.published(conclusion) : D.State}>:
  match part:
    case (u, L.Both{pos, query_result}):
      F.combined_pair(L.E<{t == Nat.add(Q.size(before), 1n) : Nat}, {w == U.published(conclusion) : D.State}>,
        {u == 1n : Nat}, {w == U.published(conclusion) : D.State},
        publication_in_end_and_unique(conclusion, closes, delivery, u, w, query_result),
        local => state => L.Both{Equal.trans(Nat, t, Nat.add(Q.size(before), u), Nat.add(Q.size(before), 1n),
          pos, Equal.cong(Nat, Nat, z => Nat.add(Q.size(before), z), u, 1n, local)), state})

law publication_unique_after_prefix:
  for +before: List<&2, Q.Frame>
  for +conclusion: N.Conclusion
  for +closes: Bool
  for +delivery: H.Delivery
  for +t: Nat
  for +w: D.State
  for without: {absent(Publication{}, before) == True{} : Bool}
  for query_result: {Q.query(Q.concatenate(before, H.render_conclusion(conclusion, closes, delivery)), t) ==
    Some{Q.Published{w}} : Maybe<&2, Q.Frame>}
  L.E<{t == Nat.add(Q.size(before), 1n) : Nat}, {w == U.published(conclusion) : D.State}>
def publication_unique_after_prefix(before, conclusion, closes, delivery, t, w, without, query_result):
  publication_located(before, conclusion, closes, delivery, t, w,
    locate_in_suffix(Publication{}, before, H.render_conclusion(conclusion, closes, delivery), t, Q.Published{w}, without, {==}, query_result))

# Atomic conclusion follows from generated order and N.conclude.
def none_publication_real(-a: I.Environment, -k: String, -x: I.Scenario, +xs: List<&2, Q.Frame>,
  without: {absent(Publication{}, xs) == True{} : Bool},
  extract: @u: Nat -> @w: D.State -> I.Happens(a, k, x, u, I.Published{w}) ->
    {Q.query(xs, u) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>}) -> K.NonePublication(a, k, x):
  +u => +w => fact => absent_excludes_query(Publication{}, xs, u, Q.Published{w}, without, {==}, extract(u, w, fact))

def conclusion_without_publication_real(-a: I.Environment, -k: String, -x: I.Scenario,
  +before: List<&2, Q.Frame>, +s: D.State, +w: D.State, +ts: List<&2, S.OperationEvent>, +r: S.Response,
  +bs: List<&2, U32>, +delivery: H.Delivery,
  without: {absent(Publication{}, before) == True{} : Bool},
  initial: {s == I.initial(x) : D.State},
  status: {U.status_success(r) == False{} : Bool},
  extract: @u: Nat -> @v: D.State -> I.Happens(a, k, x, u, I.Published{v}) ->
    {Q.query(Q.concatenate(before, H.render_final(N.Prepared{w, ts, r, bs}, s, False{}, delivery)), u) == Some{Q.Published{v}} : Maybe<&2, Q.Frame>}) ->
  L.E<{U.published(N.conclude(N.Prepared{w, ts, r, bs}, s)) == I.initial(x) : D.State}, K.NonePublication(a, k, x)>:
  F.combined_pair(L.E<{U.published(N.conclude(N.Prepared{w, ts, r, bs}, s)) == I.initial(x) : D.State}, K.NonePublication(a, k, x)>,
    {U.status_success(r) == False{} : Bool}, {U.status_success(r) == False{} : Bool},
    Call.duplicate_equality(Bool, U.status_success(r), False{}, status),
    preserves => none =>
    L.Both{Equal.trans(D.State, S.publish(r, s, w), s, I.initial(x),
      U.all_status_without_success_preserves_published(r, s, w, preserves), initial),
      none_publication_real(a, k, x, Q.concatenate(before, H.render_final(N.Prepared{w, ts, r, bs}, s, False{}, delivery)),
        concatenate_absence(Publication{}, before, H.render_final(N.Prepared{w, ts, r, bs}, s, False{}, delivery), without,
          response_negative_publish(S.publish(r, s, w), r, bs, False{}, delivery, none)), extract)})

def index_conclusion(+before: List<&2, Q.Frame>, prepared: N.Prepared, s: D.State) -> Nat:
  N.Prepared{w, ts, +r, bs} = prepared
  Nat.add(Q.size(before), Q.size(Con{Q.Prepared{r, bs}, H.render_publication(r, S.publish(r, s, w))}))

law conclusion_atomic_real:
  for -a: I.Environment
  for -k: String
  for -x: I.Scenario
  for +s: D.State
  for initial: {s == I.initial(x) : D.State}
  for +before: List<&2, Q.Frame>
  for +prepared: N.Prepared
  for +delivery: H.Delivery
  for without: {absent(Publication{}, before) == True{} : Bool}
  for introduce: @u: Nat -> @w: D.State ->
    {Q.query(Q.concatenate(before, H.render_final(prepared, s, False{}, delivery)), u) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>} ->
    I.Happens(a, k, x, u, I.Published{w})
  for extract: @u: Nat -> @w: D.State -> I.Happens(a, k, x, u, I.Published{w}) ->
    {Q.query(Q.concatenate(before, H.render_final(prepared, s, False{}, delivery)), u) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>}
  K.ConclusionAtomic(U.response(prepared), a, k, x, index_conclusion(before, prepared, s),
    U.published(N.conclude(prepared, s)))
def conclusion_atomic_real(a, k, x, s, initial, before, prepared, delivery, without, introduce, extract):
  match prepared:
    case N.Prepared{+w, ts, S.Response{S.Success{}, +v}, +bs}:
      (Nat.add(Q.size(before), 1n), L.Both{Q.order_shifted(Q.size(before), 1n, 2n, {==}),
        introduce(Nat.add(Q.size(before), 1n), w,
          Q.query_after_prefix(before, H.render_conclusion(N.Conclusion{w, S.Response{S.Success{}, v}, bs}, False{}, delivery), 1n))})
    case N.Prepared{w, ts, S.Response{S.Refusal{}, v}, bs}:
      conclusion_without_publication_real(a, k, x, before, s, w, ts, S.Response{S.Refusal{}, v}, bs, delivery, without, initial, {==}, extract)
    case N.Prepared{w, ts, S.Response{S.Input{}, v}, bs}:
      conclusion_without_publication_real(a, k, x, before, s, w, ts, S.Response{S.Input{}, v}, bs, delivery, without, initial, {==}, extract)
    case N.Prepared{w, ts, S.Response{S.Authentication{}, v}, bs}:
      conclusion_without_publication_real(a, k, x, before, s, w, ts, S.Response{S.Authentication{}, v}, bs, delivery, without, initial, {==}, extract)
    case N.Prepared{w, ts, S.Response{S.Certificate{}, v}, bs}:
      conclusion_without_publication_real(a, k, x, before, s, w, ts, S.Response{S.Certificate{}, v}, bs, delivery, without, initial, {==}, extract)
    case N.Prepared{w, ts, S.Response{S.DataError{}, v}, bs}:
      conclusion_without_publication_real(a, k, x, before, s, w, ts, S.Response{S.DataError{}, v}, bs, delivery, without, initial, {==}, extract)
    case N.Prepared{w, ts, S.Response{S.Limit{}, v}, bs}:
      conclusion_without_publication_real(a, k, x, before, s, w, ts, S.Response{S.Limit{}, v}, bs, delivery, without, initial, {==}, extract)
    case N.Prepared{w, ts, S.Response{S.Failure{}, v}, bs}:
      conclusion_without_publication_real(a, k, x, before, s, w, ts, S.Response{S.Failure{}, v}, bs, delivery, without, initial, {==}, extract)

# Request handling cannot install another instance: only InitialOk does only.
def delivery_without_start(-s: D.State, -bs: List<&2, U32>, closes: Bool, delivery: H.Delivery) ->
  {absent(StartWithProof{}, H.render_delivery(s, bs, closes, delivery)) == True{} : Bool}:
  match delivery:
    case H.Complete{next}: later_delivery_without_macros(StartWithProof{}, closes, s, next)
    case H.Broken{prefix}: {==}
    case H.PendingDelivery{}: {==}

def publication_without_start(r: S.Response, -s: D.State) ->
  {absent(StartWithProof{}, H.render_publication(r, s)) == True{} : Bool}:
  match r:
    case S.Response{S.Success{}, v}: {==}
    case S.Response{S.Refusal{}, v}: {==}
    case S.Response{S.Input{}, v}: {==}
    case S.Response{S.Authentication{}, v}: {==}
    case S.Response{S.Certificate{}, v}: {==}
    case S.Response{S.DataError{}, v}: {==}
    case S.Response{S.Limit{}, v}: {==}
    case S.Response{S.Failure{}, v}: {==}

def conclusion_without_start(conclusion: N.Conclusion, +closes: Bool, +delivery: H.Delivery) ->
  {absent(StartWithProof{}, H.render_conclusion(conclusion, closes, delivery)) == True{} : Bool}:
  match conclusion:
    case N.Conclusion{+s, +r, +bs}:
      concatenate_absence(StartWithProof{}, H.render_publication(r, s),
        Con{Q.Completed{r, s, closes}, H.render_delivery(s, bs, closes, delivery)},
        publication_without_start(r, s), delivery_without_start(s, bs, closes, delivery))

def error_framed_without_start(result: Maybe<&2, List<&2, U32>>, +r: S.Response,
  +s: D.State, +closes: Bool, +delivery: H.Delivery) ->
  {absent(StartWithProof{}, H.render_error_framed(result, r, s, closes, delivery)) == True{} : Bool}:
  match result:
    case None{}: {==}
    case Some{bs}: delivery_without_start(s, bs, closes, delivery)

def error_without_start(+status: S.Status, +s: D.State, +closes: Bool, +delivery: H.Delivery) ->
  {absent(StartWithProof{}, H.render_error(status, s, closes, delivery)) == True{} : Bool}:
  error_framed_without_start(Protocol.frame(S.response_value(S.response_error(status))), S.response_error(status), s, closes, delivery)

def failure_without_start(+s: D.State, +stage: X.Stage, +id: String, fatal: Bool, +delivery: H.Delivery) ->
  {absent(StartWithProof{}, H.render_failure(s, stage, id, fatal, delivery)) == True{} : Bool}:
  match fatal:
    case True{}: {==}
    case False{}: error_without_start(S.Failure{}, s, False{}, delivery)

def fatal_published_without_start(conclusion: N.Conclusion, +stage: X.Stage, +id: String) ->
  {absent(StartWithProof{}, H.render_fatal_published(conclusion, stage, id)) == True{} : Bool}:
  match conclusion:
    case N.Conclusion{+s, +r, bs}:
      concatenate_absence(StartWithProof{}, H.render_publication(r, s), [Q.Failed{stage, id, True{}}, Q.Closed{}], publication_without_start(r, s), {==})

law branch_without_start:
  for +m: H.Micro
  for +s: D.State
  for +branch: H.Branch
  for service: {H.starts(branch) == False{} : Bool}
  {absent(StartWithProof{}, H.render(m, s, branch)) == True{} : Bool}
def branch_without_start(m, s, branch, service):
  match branch:
    case H.InitialOk{}:
      F.absurd_boolean({absent(StartWithProof{}, H.render(m, s, H.InitialOk{})) == True{} : Bool}, Equal.sym(Bool, True{}, False{}, service))
    case H.InitialRefusal{status}: {==}
    case H.InitialFailure{accepts, stage, id, fatal}:
      match accepts:
        case True{}:
          F.absurd_boolean({absent(StartWithProof{}, H.render(m, s, H.InitialFailure{True{}, stage, id, fatal})) == True{} : Bool},
            Equal.sym(Bool, True{}, False{}, service))
        case False{}: {==}
    case H.WithoutResponse{}: {==}
    case H.InputRefusal{+error, +closes, +delivery}:
      concatenate_absence(StartWithProof{}, H.micro_input(m), H.render_error(H.status_input(error), s, closes, delivery),
        micro_input_without_macros(StartWithProof{}, m), error_without_start(H.status_input(error), s, closes, delivery))
    case H.AutRefusal{+r, +delivery}:
      concatenate_absence(StartWithProof{}, H.render_received(m, r), Q.concatenate(H.micro_authentication(m),
        Con{Q.Authenticated{r, None{}}, H.render_error(S.Authentication{}, s, False{}, delivery)}), received_without_macros(StartWithProof{}, m, r),
        concatenate_absence(StartWithProof{}, H.micro_authentication(m), Con{Q.Authenticated{r, None{}}, H.render_error(S.Authentication{}, s, False{}, delivery)},
          micro_authentication_without_macros(StartWithProof{}, m), error_without_start(S.Authentication{}, s, False{}, delivery)))
    case H.GateRefusal{+r, +ctx, +delivery}:
      concatenate_absence(StartWithProof{}, H.render_authenticated(m, r, ctx), Con{Q.Rejected{r, ctx}, H.render_error(S.Certificate{}, s, False{}, delivery)},
        authenticated_without_macros(StartWithProof{}, m, r, ctx), error_without_start(S.Certificate{}, s, False{}, delivery))
    case H.Executed{+r, +ctx, +exec, +p, +delivery}:
      concatenate_absence(StartWithProof{}, H.render_execution(m, r, ctx, exec), Q.concatenate(H.micro_output(m), H.render_final(p, s, False{}, delivery)),
        execution_host_without_macros(StartWithProof{}, m, r, ctx, exec),
        concatenate_absence(StartWithProof{}, H.micro_output(m), H.render_final(p, s, False{}, delivery), micro_output_without_macros(StartWithProof{}, m),
          conclusion_without_start(N.conclude(p, s), False{}, delivery)))
    case H.FailureBefore{+phase, +stage, +id, +fatal, +delivery}:
      concatenate_absence(StartWithProof{}, H.render_phase(m, phase), H.render_failure(s, stage, id, fatal, delivery),
        phase_previous_without_macros(StartWithProof{}, m, phase), failure_without_start(s, stage, id, fatal, delivery))
    case H.FatalAfterPublication{+r, +ctx, +exec, +p, +stage, +id}:
      concatenate_absence(StartWithProof{}, H.render_execution(m, r, ctx, exec), Q.concatenate(H.micro_output(m), H.render_fatal_published(N.conclude(p, s), stage, id)),
        execution_host_without_macros(StartWithProof{}, m, r, ctx, exec),
        concatenate_absence(StartWithProof{}, H.micro_output(m), H.render_fatal_published(N.conclude(p, s), stage, id), micro_output_without_macros(StartWithProof{}, m),
          fatal_published_without_start(N.conclude(p, s), stage, id)))
    case H.Pending{phase}: phase_previous_without_macros(StartWithProof{}, m, phase)
    case H.InitialPending{accepts}:
      match accepts:
        case True{}:
          F.absurd_boolean({absent(StartWithProof{}, H.render(m, s, H.InitialPending{True{}})) == True{} : Bool},
            Equal.sym(Bool, True{}, False{}, service))
        case False{}: {==}

law service_without_start_combined_proof:
  for ~c: S.Configuration
  for +reception: X.Reception
  for +state: List<&2, U32>
  for +s: D.State
  for +data: H.DataTools
  for +m: H.Micro
  {absent(StartWithProof{}, H.generate(c, reception, state, s, data, m)) == True{} : Bool}
def service_without_start_combined_proof(c, reception, state, s, data, m):
  branch_without_start(m, s, H.decide(c, reception, state, data), H.service_negative_starts(c, reception, state, data))

# Initialization progress: the point is generated, not postulated by Processable.
law initialization_encoded_has_instance:
  for ~c: S.Configuration
  for +id: String
  for +s: D.State
  for +m: H.Micro
  for +bs: List<&2, U32>
  for configured: {Config.is_valid(c, id) == True{} : Bool}
  for encoded: {Protocol.encode(D.state_value(s)) == Some{bs} : Maybe<&2, List<&2, U32>>}
  exs t: Nat
  {Q.query(H.generate_initial(c, id, s, H.Accepted{}, m), t) == Some{Q.Initialized{s}} : Maybe<&2, Q.Frame>}
def initialization_encoded_has_instance(c, id, s, m, bs, configured, encoded):
  (2n+Nat.add(Q.size(H.micro_output(m)), 2n),
    Equal.trans(Maybe<&2, Q.Frame>,
      Q.query(H.generate_initial(c, id, s, H.Accepted{}, m), 2n+Nat.add(Q.size(H.micro_output(m)), 2n)),
      Q.query(H.render(m, s, H.InitialOk{}), 2n+Nat.add(Q.size(H.micro_output(m)), 2n)), Some{Q.Initialized{s}},
      Equal.cong(Bool, Maybe<&2, Q.Frame>, ok => Q.query(H.render(m, s, H.decide_initial_cases(ok, H.Accepted{})),
        2n+Nat.add(Q.size(H.micro_output(m)), 2n)), Config.is_valid(c, id), True{}, configured),
      Equal.trans(Maybe<&2, Q.Frame>,
        Q.query(Q.concatenate(H.micro_output(m), H.render_initial(Protocol.encode(D.state_value(s)), s)), Nat.add(Q.size(H.micro_output(m)), 2n)),
        Q.query(H.render_initial(Protocol.encode(D.state_value(s)), s), 2n), Some{Q.Initialized{s}},
        Q.query_after_prefix(H.micro_output(m), H.render_initial(Protocol.encode(D.state_value(s)), s), 2n),
        Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, Q.Frame>, result => Q.query(H.render_initial(result, s), 2n),
          Protocol.encode(D.state_value(s)), Some{bs}, encoded))))

def start_seed_encoded(~c: S.Configuration, +id: String, +s: D.State, +m: H.Micro,
  configured: {Config.is_valid(c, id) == True{} : Bool},
  assembled: Proposal.Assembled(Protocol.encode(D.state_value(s)), Nil{})) ->
  &t: Nat -> {Q.query(H.generate_initial(c, id, s, H.Accepted{}, m), t) == Some{Q.Initialized{s}} : Maybe<&2, Q.Frame>}:
  match assembled:
    case (bs, packet, L.Both{encoded, rest}): initialization_encoded_has_instance(c, id, s, m, bs, configured, encoded)

law seed_valid_has_instance_after_approval:
  for ~c: S.Configuration
  for +id: String
  for +s: D.State
  for +m: H.Micro
  for configured: {Config.is_valid(c, id) == True{} : Bool}
  for valid: R.Valid(c, s)
  exs t: Nat
  {Q.query(H.generate_initial(c, id, s, H.Accepted{}, m), t) == Some{Q.Initialized{s}} : Maybe<&2, Q.Frame>}
def seed_valid_has_instance_after_approval(c, id, s, m, configured, valid):
  F.combined_pair((&t: Nat -> {Q.query(H.generate_initial(c, id, s, H.Accepted{}, m), t) == Some{Q.Initialized{s}} : Maybe<&2, Q.Frame>}),
    {Config.is_valid(c, id) == True{} : Bool}, {Config.is_valid(c, id) == True{} : Bool},
    Call.duplicate_equality(Bool, Config.is_valid(c, id), True{}, configured),
    official => starts =>
      start_seed_encoded(c, id, s, m, starts,
        Proposal.success_valid_has_proposal_real(c, s, D.VAbsent{}, Nil{},
          L.and_left({R.configuration_is_valid(c) == True{} : Bool}, {S.environment(c) == id : String},
            Configuration.accepts_requires_structure_and_identity_exact(c, id, official)), valid)))

# Only valid configuration and the Accepted judgment emit these milestones.
def true_se_false_impossible(b: Bool, impossible: {b == False{} : Bool} -> Empty) -> {b == True{} : Bool}:
  match b:
    case False{}: L.ex_false({False{} == True{} : Bool}, impossible({==}))
    case True{}: {==}

def query_of_start_requires_mark(+m: H.Micro, +s: D.State, +branch: H.Branch, +t: Nat, +q: Q.Frame,
  kind: {of_that_kind(StartWithProof{}, q) == True{} : Bool},
  query_result: {Q.query(H.render(m, s, branch), t) == Some{q} : Maybe<&2, Q.Frame>}) -> {H.starts(branch) == True{} : Bool}:
  true_se_false_impossible(H.starts(branch), negative =>
    absent_excludes_query(StartWithProof{}, H.render(m, s, branch), t, q, branch_without_start(m, s, branch, negative), kind, query_result))

def mark_initial_requires_is_valid(result: H.ResultInitial, +is_valid: Bool,
  mark: {H.starts(H.decide_accepted_initial(result, is_valid)) == True{} : Bool}) -> {is_valid == True{} : Bool}:
  match result:
    case H.InitializationFinished{}:
      match is_valid:
        case False{}: F.absurd_boolean({False{} == True{} : Bool}, mark)
        case True{}: {==}
    case H.FailedInitial{accepts, stage, id, fatal}: F.and_boolean_right(accepts, is_valid, mark)
    case H.PendingInitial{accepts}: F.and_boolean_right(accepts, is_valid, mark)

def mark_initial_requires_judgment(+is_valid: Bool, +judgment: H.Judgment, +result: H.ResultInitial,
  mark: {H.starts(H.decide_judgment_initial(judgment, result, is_valid)) == True{} : Bool}) ->
  L.E<{is_valid == True{} : Bool}, {judgment == H.Accepted{} : H.Judgment}>:
  match judgment:
    case H.Accepted{}: L.Both{mark_initial_requires_is_valid(result, is_valid, mark), {==}}
    case H.Refused{}: F.absurd_boolean(L.E<{is_valid == True{} : Bool}, {H.Refused{} == H.Accepted{} : H.Judgment}>, mark)
    case H.ErrorJudgment{id, fatal}: F.absurd_boolean(L.E<{is_valid == True{} : Bool}, {H.ErrorJudgment{id, fatal} == H.Accepted{} : H.Judgment}>, mark)
    case H.PendingJudgment{}: F.absurd_boolean(L.E<{is_valid == True{} : Bool}, {H.PendingJudgment{} == H.Accepted{} : H.Judgment}>, mark)

def start_result_requires_configuration_and_judgment_accepted(+m: H.Micro, +s: D.State,
  +is_valid: Bool, +judgment: H.Judgment, +result: H.ResultInitial, +t: Nat, +q: Q.Frame,
  kind: {of_that_kind(StartWithProof{}, q) == True{} : Bool},
  query_result: {Q.query(H.render(m, s, H.decide_judgment_initial(judgment, result, is_valid)), t) == Some{q} : Maybe<&2, Q.Frame>}) ->
  L.E<{is_valid == True{} : Bool}, {judgment == H.Accepted{} : H.Judgment}>:
  mark_initial_requires_judgment(is_valid, judgment, result,
    query_of_start_requires_mark(m, s, H.decide_judgment_initial(judgment, result, is_valid), t, q, kind, query_result))

law start_requires_configuration_and_judgment_accepted:
  for +m: H.Micro
  for +s: D.State
  for is_valid: Bool
  for +judgment: H.Judgment
  for +t: Nat
  for +q: Q.Frame
  for kind: {of_that_kind(StartWithProof{}, q) == True{} : Bool}
  for query_result: {Q.query(H.render(m, s, H.decide_initial_cases(is_valid, judgment)), t) == Some{q} : Maybe<&2, Q.Frame>}
  L.E<{is_valid == True{} : Bool}, {judgment == H.Accepted{} : H.Judgment}>
def start_requires_configuration_and_judgment_accepted(m, s, is_valid, judgment, t, q, kind, query_result):
  start_result_requires_configuration_and_judgment_accepted(m, s, is_valid, judgment, H.InitializationFinished{}, t, q, kind, query_result)

def initial_accepts_before_of_part(+m: H.Micro, +s: D.State, -t: Nat, -w: D.State,
  part: &u: Nat -> L.E<{t == 2n+u : Nat},
    {Q.query(Q.concatenate(H.micro_output(m), H.render_initial(Protocol.encode(D.state_value(s)), s)), u) == Some{Q.Initialized{w}} : Maybe<&2, Q.Frame>}>) ->
  &a: Nat -> L.E<{Nat.is_lt(a, t) == True{} : Bool},
    {Q.query(H.render(m, s, H.InitialOk{}), a) == Some{Q.InitialAccepts{}} : Maybe<&2, Q.Frame>}>:
  match part:
    case (u, L.Both{pos, query_result}):
      (1n, L.Both{(%Equal.sym(Nat, t, 2n+u, pos) : {Nat.is_lt(1n, _) == True{} : Bool} {==}), {==}})

law instance_only_starts_after_proof_initial:
  for +m: H.Micro
  for +s: D.State
  for +t: Nat
  for +w: D.State
  for query_result: {Q.query(H.render(m, s, H.InitialOk{}), t) == Some{Q.Initialized{w}} : Maybe<&2, Q.Frame>}
  exs a: Nat
  L.E<{Nat.is_lt(a, t) == True{} : Bool},
    {Q.query(H.render(m, s, H.InitialOk{}), a) == Some{Q.InitialAccepts{}} : Maybe<&2, Q.Frame>}>
def instance_only_starts_after_proof_initial(m, s, t, w, query_result):
  initial_accepts_before_of_part(m, s, t, w,
    locate_in_suffix(Initialization{}, [Q.Configured{}, Q.InitialAccepts{}],
      Q.concatenate(H.micro_output(m), H.render_initial(Protocol.encode(D.state_value(s)), s)), t, Q.Initialized{w}, {==}, {==}, query_result))

def exclude_origin_without_store(+xs: List<&2, Q.Frame>, +t: Nat, +w: D.State,
  without_publish: {absent(Publication{}, xs) == True{} : Bool},
  without_start: {absent(Initialization{}, xs) == True{} : Bool}, origin: OriginGeneral(xs, t, None{}, w)) -> Empty:
  match origin:
    case L.Left{L.Both{equal, none}}: F.none_negative_some(D.State, w, equal)
    case L.Right{L.Left{(u, L.Both{order, query_result})}}:
      absent_excludes_query(Publication{}, xs, u, Q.Published{w}, without_publish, {==}, query_result)
    case L.Right{L.Right{(u, L.Both{order, query_result})}}:
      absent_excludes_query(Initialization{}, xs, u, Q.Initialized{w}, without_start, {==}, query_result)

def without_store_negative_exists_state(+xs: List<&2, Q.Frame>, +t: Nat, +w: D.State,
  without_publish: {absent(Publication{}, xs) == True{} : Bool},
  without_start: {absent(Initialization{}, xs) == True{} : Bool},
  seen: {Q.state_in(xs, t, None{}) == Some{w} : Maybe<&2, D.State>}) -> Empty:
  exclude_origin_without_store(xs, t, w, without_publish, without_start, origin_general_of_state_visible(t, xs, None{}, w, seen))

def prefix_initial_without_store(+m: H.Micro, accepts: Bool) ->
  L.E<{absent(Publication{}, H.prefix_initial(m, accepts)) == True{} : Bool},
    {absent(Initialization{}, H.prefix_initial(m, accepts)) == True{} : Bool}>:
  match accepts:
    case False{}: L.Both{{==}, {==}}
    case True{}: L.Both{micro_output_without_macros(Publication{}, m), micro_output_without_macros(Initialization{}, m)}

# A failing or pending initialization worker never installs the instance.
def failure_initial_without_instance(+m: H.Micro, +s: D.State, +accepts: Bool, +stage: X.Stage, +id: String, +fatal: Bool) ->
  {absent(Initialization{}, H.render(m, s, H.InitialFailure{accepts, stage, id, fatal})) == True{} : Bool}:
  concatenate_absence(Initialization{}, H.prefix_initial(m, accepts),
    [Q.Failed{stage, id, fatal}, Q.InitialRefused{S.Failure{}}],
    L.and_right({absent(Publication{}, H.prefix_initial(m, accepts)) == True{} : Bool},
      {absent(Initialization{}, H.prefix_initial(m, accepts)) == True{} : Bool}, prefix_initial_without_store(m, accepts)), {==})

def pending_initial_without_instance(+m: H.Micro, +s: D.State, +accepts: Bool) ->
  {absent(Initialization{}, H.render(m, s, H.InitialPending{accepts})) == True{} : Bool}:
  L.and_right({absent(Publication{}, H.prefix_initial(m, accepts)) == True{} : Bool},
    {absent(Initialization{}, H.prefix_initial(m, accepts)) == True{} : Bool}, prefix_initial_without_store(m, accepts))

def prefix_initial_negative_has_state(+m: H.Micro, +accepts: Bool, +rest: List<&2, Q.Frame>, +t: Nat, +w: D.State,
  without_pub: {absent(Publication{}, rest) == True{} : Bool}, without_start: {absent(Initialization{}, rest) == True{} : Bool},
  seen: {Q.state_in(Con{Q.Configured{}, Q.concatenate(H.prefix_initial(m, accepts), rest)}, t, None{}) == Some{w} : Maybe<&2, D.State>}) -> Empty:
  F.combined_pair(Empty, {absent(Publication{}, H.prefix_initial(m, accepts)) == True{} : Bool},
    {absent(Initialization{}, H.prefix_initial(m, accepts)) == True{} : Bool}, prefix_initial_without_store(m, accepts),
    publication => start => without_store_negative_exists_state(Con{Q.Configured{}, Q.concatenate(H.prefix_initial(m, accepts), rest)}, t, w,
      concatenate_absence(Publication{}, H.prefix_initial(m, accepts), rest, publication, without_pub),
      concatenate_absence(Initialization{}, H.prefix_initial(m, accepts), rest, start, without_start), seen))

def prefix_initial_direct_negative_has_state(+m: H.Micro, +accepts: Bool, +t: Nat, +w: D.State,
  seen: {Q.state_in(Con{Q.Configured{}, H.prefix_initial(m, accepts)}, t, None{}) == Some{w} : Maybe<&2, D.State>}) -> Empty:
  F.combined_pair(Empty, {absent(Publication{}, H.prefix_initial(m, accepts)) == True{} : Bool},
    {absent(Initialization{}, H.prefix_initial(m, accepts)) == True{} : Bool}, prefix_initial_without_store(m, accepts),
    publication => start => without_store_negative_exists_state(Con{Q.Configured{}, H.prefix_initial(m, accepts)}, t, w, publication, start, seen))

def origin_of_result_initial_cases(+m: H.Micro, +s: D.State, +judgment: H.Judgment, +result: H.ResultInitial, +is_valid: Bool, +t: Nat, +w: D.State,
  seen: {Q.state_in(H.render(m, s, H.decide_judgment_initial(judgment, result, is_valid)), t, None{}) == Some{w} : Maybe<&2, D.State>}) ->
  Origin(H.render(m, s, H.decide_judgment_initial(judgment, result, is_valid)), t, s, w):
  match judgment:
    case H.Accepted{}:
      match result:
        case H.InitializationFinished{}:
          match is_valid:
            case False{}: L.ex_false(Origin(H.render(m, s, H.InitialRefusal{S.DataError{}}), t, s, w), without_store_negative_exists_state([Q.Configured{}, Q.InitialRefused{S.DataError{}}], t, w, {==}, {==}, seen))
            case True{}: origin_of_state_initialized(t, m, s, w, seen)
        case H.FailedInitial{+accepts, +stage, +id, +fatal}:
          L.ex_false(Origin(H.render(m, s, H.InitialFailure{accepts && is_valid, stage, id, fatal}), t, s, w),
            prefix_initial_negative_has_state(m, accepts && is_valid, [Q.Failed{stage, id, fatal}, Q.InitialRefused{S.Failure{}}], t, w, {==}, {==}, seen))
        case H.PendingInitial{+accepts}:
          L.ex_false(Origin(H.render(m, s, H.InitialPending{accepts && is_valid}), t, s, w), prefix_initial_direct_negative_has_state(m, accepts && is_valid, t, w, seen))
    case H.Refused{}: L.ex_false(Origin(H.render(m, s, H.InitialRefusal{S.Certificate{}}), t, s, w), without_store_negative_exists_state([Q.Configured{}, Q.InitialRefused{S.Certificate{}}], t, w, {==}, {==}, seen))
    case H.ErrorJudgment{+id, +fatal}:
      L.ex_false(Origin(H.render(m, s, H.InitialFailure{False{}, X.Verify{}, id, fatal}), t, s, w), without_store_negative_exists_state([Q.Configured{}, Q.Failed{X.Verify{}, id, fatal}, Q.InitialRefused{S.Failure{}}], t, w, {==}, {==}, seen))
    case H.PendingJudgment{}: L.ex_false(Origin(H.render(m, s, H.InitialPending{False{}}), t, s, w), without_store_negative_exists_state([Q.Configured{}], t, w, {==}, {==}, seen))

def origin_of_state_initial_cases(+m: H.Micro, +s: D.State, +is_valid: Bool, +judgment: H.Judgment, +t: Nat, +w: D.State,
  seen: {Q.state_in(H.render(m, s, H.decide_initial_cases(is_valid, judgment)), t, None{}) == Some{w} : Maybe<&2, D.State>}) ->
  Origin(H.render(m, s, H.decide_initial_cases(is_valid, judgment)), t, s, w):
  origin_of_result_initial_cases(m, s, judgment, H.InitializationFinished{}, is_valid, t, w, seen)


def OfCode(r: S.Response) -> Type:
  match r:
    case S.Response{S.Success{}, v}: Unit
    case S.Response{S.Refusal{}, v}: Unit
    case S.Response{S.DataError{}, v}: Unit
    case _: Empty

def MachineOfCode(m: N.Machine) -> Type:
  match m:
    case N.Running{w, a, ts}: Unit
    case N.Stopped{w, ts, r}: OfCode(r)

def TraceOfCode(p: S.Trace) -> Type:
  match p:
    case S.Prefix{w, ts}: Unit
    case S.Final{w, ts, r}: OfCode(r)

def operation_negative_fabricates_status(+n: Nat, r: D.ResultOp, w: D.State,
  o: D.Operation, k: S.Return -> S.Action, ts: List<&2, S.OperationEvent>, +e: D.Schema,
  induction: @m: N.Machine -> MachineOfCode(m) -> TraceOfCode(N.traverse(n, m, e))) ->
  TraceOfCode(N.traverse(n, N.step_machine(S.apply(r, w, o, k), ts), e)):
  match r:
    case D.FailureData{}:
      induction(N.Stopped{w, S.append(ts, S.OperationEvent{o, S.ErrorOfData{}}), S.response_error(S.DataError{})}, Unit{})
    case D.Observed{+v}:
      induction(N.Running{w, k(S.Datum{v}), S.append(ts, S.OperationEvent{o, S.Reading{v}})}, Unit{})
    case D.Changed{s}:
      induction(N.Running{s, k(S.UnitValue{}), S.append(ts, S.OperationEvent{o, S.Write{}})}, Unit{})

law execution_trace_negative_fabricates_status_of_host:
  for n: Nat
  for m: N.Machine
  for +e: D.Schema
  for h: MachineOfCode(m)
  TraceOfCode(N.traverse(n, m, e))

def execution_trace_negative_fabricates_status_of_host(n, m, e, h):
  match n m:
    case 0n N.Running{w, a, ts}: Unit{}
    case 0n N.Stopped{w, ts, r}: h
    case 1n+ +j N.Running{+w, a, ts}:
      match a:
        case S.Finish{v}:
          execution_trace_negative_fabricates_status_of_host(j, N.Stopped{w, ts, S.Response{S.Success{}, v}}, e, Unit{})
        case S.Refuse{v}:
          execution_trace_negative_fabricates_status_of_host(j, N.Stopped{w, ts, S.Response{S.Refusal{}, v}}, e, Unit{})
        case S.Access{+o, k}: operation_negative_fabricates_status(j, D.operate(e, w, o), w, o, k, ts, e, next => allowed => execution_trace_negative_fabricates_status_of_host(j, next, e, allowed))
    case 1n+j N.Stopped{w, ts, r}:
      execution_trace_negative_fabricates_status_of_host(j, N.Stopped{w, ts, r}, e, h)

def OfFinal(r: S.Response) -> Type:
  match r:
    case S.Response{S.Success{}, v}: Unit
    case S.Response{S.Refusal{}, v}: Unit
    case S.Response{S.DataError{}, v}: Unit
    case S.Response{S.Limit{}, v}: Unit
    case _: Empty

def response_technique_only_data_or_limit(ok: Bool, fits: Bool, -r: S.Response, h: OfFinal(r)) ->
  OfFinal(R.response_technique_cases(ok, fits, r)):
  match ok fits:
    case False{} _: Unit{}
    case True{} False{}: Unit{}
    case True{} True{}: h

def state_technical_only_data_or_limit(ok: Bool, fits: Bool, -r: S.Response, h: OfFinal(r)) ->
  OfFinal(R.state_technical_cases(ok, fits, r)):
  match ok fits:
    case False{} _: Unit{}
    case True{} False{}: Unit{}
    case True{} True{}: h

law finalize_only_appends_data_or_limit:
  for proposal: S.Response
  for c: S.Configuration
  for +w: D.State
  for h: OfCode(proposal)
  OfFinal(R.finalize(proposal, c, w))
def finalize_only_appends_data_or_limit(proposal, c, w, h):
  match proposal c:
    case S.Response{S.Success{}, +v} S.Configuration{+e, laws, +lim, amb}:
      state_technical_only_data_or_limit(D.structure(e, w), R.fits(R.limit_state(lim), D.state_value(w)),
        R.response_technique_cases(D.value_valid(v), R.fits(R.limit_response(lim), S.response_value(S.Response{S.Success{}, v})), S.Response{S.Success{}, v}),
        response_technique_only_data_or_limit(D.value_valid(v), R.fits(R.limit_response(lim), S.response_value(S.Response{S.Success{}, v})), S.Response{S.Success{}, v}, Unit{}))
    case S.Response{S.Refusal{}, +v} S.Configuration{e, laws, +lim, amb}:
      response_technique_only_data_or_limit(D.value_valid(v), R.fits(R.limit_response(lim), S.response_value(S.Response{S.Refusal{}, v})), S.Response{S.Refusal{}, v}, Unit{})
    case S.Response{S.DataError{}, v} S.Configuration{e, laws, lim, amb}: Unit{}
    case S.Response{S.Input{}, v} _: match h:
    case S.Response{S.Authentication{}, v} _: match h:
    case S.Response{S.Certificate{}, v} _: match h:
    case S.Response{S.Limit{}, v} _: match h:
    case S.Response{S.Failure{}, v} _: match h:

def negate_start_implies_negate_instance(q: Q.Frame, h: {Bool.not(of_that_kind(StartWithProof{}, q)) == True{} : Bool}) ->
  {Bool.not(of_that_kind(Initialization{}, q)) == True{} : Bool}:
  match q:
    case Q.Configured{}: {==}
    case Q.InitialAccepts{}: {==}
    case Q.Initialized{s}: h
    case Q.InitialRefused{s}: {==}
    case Q.Encoded{v, bs}: {==}
    case Q.Decoded{bs, v}: {==}
    case Q.Stored{s, bs, a}: {==}
    case Q.Checked{pos, n}: {==}
    case Q.Constructed{pos, n}: {==}
    case Q.Read{a, n, d}: {==}
    case Q.Received{r}: {==}
    case Q.Authenticated{r, ctx}: {==}
    case Q.Accepts{r, ctx}: {==}
    case Q.Rejected{r, ctx}: {==}
    case Q.Started{r, ctx}: {==}
    case Q.Evaluated{r, ctx, p}: {==}
    case Q.Operated{e, s, o, r}: {==}
    case Q.Prepared{r, bs}: {==}
    case Q.Published{s}: {==}
    case Q.Visible{s}: {==}
    case Q.Failed{stage, id, fatal}: {==}
    case Q.Completed{r, s, f}: {==}
    case Q.Delivered{bs}: {==}
    case Q.Interrupted{bs}: {==}
    case Q.Closed{}: {==}
    case Q.Next{a, b}: {==}
    case Q.Inspection{d}: {==}
    case Q.Effect{d}: {==}

def without_start_includes_without_instance(+xs: List<&2, Q.Frame>, h: {absent(StartWithProof{}, xs) == True{} : Bool}) ->
  {absent(Initialization{}, xs) == True{} : Bool}:
  match xs:
    case Nil{}: {==}
    case Con{+q, +t}:
      F.combined_pair({absent(Initialization{}, Con{q, t}) == True{} : Bool},
        {Bool.not(of_that_kind(StartWithProof{}, q)) == True{} : Bool}, {absent(StartWithProof{}, t) == True{} : Bool},
        F.and_boolean_separate(Bool.not(of_that_kind(StartWithProof{}, q)), absent(StartWithProof{}, t), h),
        head => tail => F.and_boolean_intro(Bool.not(of_that_kind(Initialization{}, q)), absent(Initialization{}, t),
          negate_start_implies_negate_instance(q, head), without_start_includes_without_instance(t, tail)))

law service_without_start:
  for ~c: S.Configuration
  for +reception: X.Reception
  for +state: List<&2, U32>
  for +s: D.State
  for +data: H.DataTools
  for +m: H.Micro
  {absent(Initialization{}, H.generate(c, reception, state, s, data, m)) == True{} : Bool}
def service_without_start(c, reception, state, s, data, m):
  without_start_includes_without_instance(H.generate(c, reception, state, s, data, m), service_without_start_combined_proof(c, reception, state, s, data, m))

# Invert conclusion in the complete trace and its corresponding Rule6.
def conclusion_located(+before: List<&2, Q.Frame>, +state: D.State, +response: S.Response,
  +bytes: List<&2, U32>, +delivery: H.Delivery, -t: Nat, +q: Q.Frame,
  target: {of_that_kind(Conclusion{}, q) == True{} : Bool},
  part: &u: Nat -> L.E<{t == Nat.add(Q.size(before), u) : Nat},
    {Q.query(H.render_conclusion(N.Conclusion{state, response, bytes}, False{}, delivery), u) == Some{q} : Maybe<&2, Q.Frame>}>) ->
  L.E<{t == Nat.add(Q.size(before), Q.size(Con{Q.Prepared{response, bytes}, H.render_publication(response, state)})) : Nat},
    {q == Q.Completed{response, state, False{}} : Q.Frame}>:
  match part:
    case (u, L.Both{pos, query_result}):
      F.combined_pair(
        L.E<{t == Nat.add(Q.size(before), Q.size(Con{Q.Prepared{response, bytes}, H.render_publication(response, state)})) : Nat},
          {q == Q.Completed{response, state, False{}} : Q.Frame}>,
        {u == Q.size(Con{Q.Prepared{response, bytes}, H.render_publication(response, state)}) : Nat},
        {q == Q.Completed{response, state, False{}} : Q.Frame},
        conclusion_in_end_and_unique(state, response, bytes, False{}, delivery, u, q, target, query_result),
        local => frame => L.Both{Equal.trans(Nat, t, Nat.add(Q.size(before), u),
          Nat.add(Q.size(before), Q.size(Con{Q.Prepared{response, bytes}, H.render_publication(response, state)})), pos,
          Equal.cong(Nat, Nat, i => Nat.add(Q.size(before), i), u,
            Q.size(Con{Q.Prepared{response, bytes}, H.render_publication(response, state)}), local)), frame})

def conclusion_unique_after_prefix(+before: List<&2, Q.Frame>, +s: D.State, +p: N.Prepared,
  +delivery: H.Delivery, +t: Nat, +q: Q.Frame,
  without: {absent(Conclusion{}, before) == True{} : Bool},
  target: {of_that_kind(Conclusion{}, q) == True{} : Bool},
  query_result: {Q.query(Q.concatenate(before, H.render_final(p, s, False{}, delivery)), t) == Some{q} : Maybe<&2, Q.Frame>}) ->
  L.E<{t == index_conclusion(before, p, s) : Nat},
    {q == Q.Completed{U.response(p), U.published(N.conclude(p, s)), False{}} : Q.Frame}>:
  match p:
    case N.Prepared{+w, ts, +r, +bs}:
      F.combined_pair(
        L.E<{t == index_conclusion(before, N.Prepared{w, ts, r, bs}, s) : Nat},
          {q == Q.Completed{r, S.publish(r, s, w), False{}} : Q.Frame}>,
        {of_that_kind(Conclusion{}, q) == True{} : Bool}, {of_that_kind(Conclusion{}, q) == True{} : Bool},
        Call.duplicate_equality(Bool, of_that_kind(Conclusion{}, q), True{}, target),
        local => prefix => conclusion_located(before, S.publish(r, s, w), r, bs, delivery, t, q, local,
          locate_in_suffix(Conclusion{}, before, H.render_final(N.Prepared{w, ts, r, bs}, s, False{}, delivery), t, q, without, prefix, query_result)))

def Rule6Conclusion(-a: I.Environment, -k: String, -x: I.Scenario, -t: Nat, q: Q.Frame) -> Type:
  match q:
    case Q.Completed{r, s, closes}: K.Rule6(I.Concluded{r, s, closes}, a, k, x, t)
    case _: Unit

def conclusion_rule6_of_equalities(-a: I.Environment, -k: String, -x: I.Scenario,
  +s: D.State, +before: List<&2, Q.Frame>, +p: N.Prepared, -t: Nat, +q: Q.Frame,
  equal: L.E<{t == index_conclusion(before, p, s) : Nat},
    {q == Q.Completed{U.response(p), U.published(N.conclude(p, s)), False{}} : Q.Frame}>,
  atomic: K.ConclusionAtomic(U.response(p), a, k, x, index_conclusion(before, p, s), U.published(N.conclude(p, s)))) ->
  Rule6Conclusion(a, k, x, t, q):
  match equal:
    case L.Both{pos, frame}:
      %Equal.sym(Nat, t, index_conclusion(before, p, s), pos) : Rule6Conclusion(a, k, x, _, q)
      %Equal.sym(Q.Frame, q, Q.Completed{U.response(p), U.published(N.conclude(p, s)), False{}}, frame) : Rule6Conclusion(a, k, x, index_conclusion(before, p, s), _)
      atomic

law conclusion_reflected_obeys_rule6:
  for -a: I.Environment
  for -k: String
  for -x: I.Scenario
  for +s: D.State
  for initial: {s == I.initial(x) : D.State}
  for +before: List<&2, Q.Frame>
  for +p: N.Prepared
  for +delivery: H.Delivery
  for +t: Nat
  for +r: S.Response
  for +published: D.State
  for +closes: Bool
  for without_publish: {absent(Publication{}, before) == True{} : Bool}
  for without_conclude: {absent(Conclusion{}, before) == True{} : Bool}
  for query_result: {Q.query(Q.concatenate(before, H.render_final(p, s, False{}, delivery)), t) == Some{Q.Completed{r, published, closes}} : Maybe<&2, Q.Frame>}
  for introduce: @u: Nat -> @w: D.State ->
    {Q.query(Q.concatenate(before, H.render_final(p, s, False{}, delivery)), u) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>} -> I.Happens(a, k, x, u, I.Published{w})
  for extract: @u: Nat -> @w: D.State -> I.Happens(a, k, x, u, I.Published{w}) ->
    {Q.query(Q.concatenate(before, H.render_final(p, s, False{}, delivery)), u) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>}
  K.Rule6(I.Concluded{r, published, closes}, a, k, x, t)
def conclusion_reflected_obeys_rule6(a, k, x, s, initial, before, p, delivery, t, r, published, closes,
  without_publish, without_conclude, query_result, introduce, extract):
  conclusion_rule6_of_equalities(a, k, x, s, before, p, t, Q.Completed{r, published, closes},
    conclusion_unique_after_prefix(before, s, p, delivery, t, Q.Completed{r, published, closes}, without_conclude, {==}, query_result),
    conclusion_atomic_real(a, k, x, s, initial, before, p, delivery, without_publish, introduce, extract))

law response_of_program_justifies_o_status_real:
  for -a: I.Environment
  for -k: String
  for -x: I.Scenario
  for -t: Nat
  for +r: S.Response
  for +w: D.State
  for status: OfFinal(r)
  for program: I.ResponseOfProgram(a, k, x, t, r, w)
  I.ResponseJustified(r, a, k, x, t)
def response_of_program_justifies_o_status_real(a, k, x, t, r, w, status, program):
  match r:
    case S.Response{S.Success{}, v}: (w, program)
    case S.Response{S.Refusal{}, v}: (w, program)
    case S.Response{S.DataError{}, v}: (w, program)
    case S.Response{S.Limit{}, v}: L.Right{(w, program)}
    case S.Response{S.Input{}, v}: match status:
    case S.Response{S.Authentication{}, v}: match status:
    case S.Response{S.Certificate{}, v}: match status:
    case S.Response{S.Failure{}, v}: match status:
