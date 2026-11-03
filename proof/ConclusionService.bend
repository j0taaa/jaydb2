# Order, response and uniqueness of actual conclusion; reception supplies correct closure.
import Base
import ./Law34Service.bend as Adm
import ./CodecOctets.bend as Octets
import ./InputService.bend as Causes
import ../src/Codec.bend as Codec
import ../contract/Bytes.bend as B
import ./ChannelService.bend as Channel
import ./LinkageService.bend as Lig
import ./VisibilityService.bend as Vis
import ../contract/Resources.bend as X
import ../src/Input.bend as Input
import ../src/Transport.bend as Transport
import ./Law2Service.bend as Two
import ./ClosuresService.bend as Closures
import ./ErrorsFixed.bend as Errors
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Interface.bend as I
import ../contract/LAWS.bend as K
import ../contract/Logic.bend as L
import ./PhasesService.bend as Phases
import ./ProtocolService.bend as Q
import ./RoutesService.bend as H
import ./Publication.bend as U
import ./Preparation.bend as Preparation
import ./Foundations.bend as F
import ./Call.bend as Call
import ../src/Core.bend as N

import ../contract/Requirements.bend as R
import ./Law5Service.bend as Law5
import ../contract/Protocol.bend as P
import ./SourceService.bend as Source
import ./ExecutionService.bend as Exec

import ./HistoryService.bend as History



def response_completed(q: Q.Frame) -> Maybe<&2, S.Response>:
  match q:
    case Q.Completed{r, s, closes}: Some{r}
    case _: None{}

def state_completed(q: Q.Frame) -> Maybe<&2, D.State>:
  match q:
    case Q.Completed{r, s, closes}: Some{s}
    case _: None{}

def fact_of_conclusion(q: Q.Frame) -> I.Fact:
  match q:
    case Q.Completed{r, s, closes}: I.Concluded{r, s, closes}
    case _: I.ClosedChannel{}

# The response below is linked to the last ACTUAL evaluation of the same path.
law last_evaluation_of_result_real:
  for ~source: Source.Source
  for ~c: S.Configuration
  for +s: D.State
  for +req: P.Request
  for +ctx: D.Context
  for +origin: Source.JudgmentSyntactic
  for +n: Nat
  for +w: D.State
  for +ts: List<&2, S.OperationEvent>
  for +proposal: S.Response
  for +frames: List<&2, Q.FrameExec>
  for sequence: {frames == Exec.generate(n, N.start(Source.program(source, origin), ctx, I.arguments(req), s), S.schema(c)) : List<&2, Q.FrameExec>}
  for result: {N.traverse(n, N.start(Source.program(source, origin), ctx, I.arguments(req), s), S.schema(c)) == S.Final{w, ts, proposal} : S.Trace}
  exs i: Nat
  {Exec.query(frames, i) == Some{Q.Evaluation{S.Final{w, ts, proposal}}} : Maybe<&2, Q.FrameExec>}
def last_evaluation_of_result_real(source, c, s, req, ctx, origin, n, w, ts, proposal, frames, sequence, result):
  Exec.last_present_has_index(frames, Q.Evaluation{S.Final{w, ts, proposal}},
    Equal.trans(Maybe<&2, Q.FrameExec>, Exec.last(frames),
      Exec.last(Exec.generate(n, N.start(Source.program(source, origin), ctx, I.arguments(req), s), S.schema(c))),
      Some{Q.Evaluation{S.Final{w, ts, proposal}}},
      Equal.cong(List<&2, Q.FrameExec>, Maybe<&2, Q.FrameExec>, Exec.last,
        frames, Exec.generate(n, N.start(Source.program(source, origin), ctx, I.arguments(req), s), S.schema(c)), sequence),
      Equal.trans(Maybe<&2, Q.FrameExec>,
        Exec.last(Exec.generate(n, N.start(Source.program(source, origin), ctx, I.arguments(req), s), S.schema(c))),
        Some{Q.Evaluation{N.traverse(n, N.start(Source.program(source, origin), ctx, I.arguments(req), s), S.schema(c))}},
        Some{Q.Evaluation{S.Final{w, ts, proposal}}},
        Exec.last_represents_all_execution_trace(n, N.start(Source.program(source, origin), ctx, I.arguments(req), s), S.schema(c)),
        Equal.cong(S.Trace, Maybe<&2, Q.FrameExec>, p => Some{Q.Evaluation{p}},
          N.traverse(n, N.start(Source.program(source, origin), ctx, I.arguments(req), s), S.schema(c)), S.Final{w, ts, proposal}, result))))

law less_that_sum_by_right:
  for a: Nat
  for b: Nat
  for -c: Nat
  for less: {Nat.is_lt(a, b) == True{} : Bool}
  {Nat.is_lt(a, Nat.add(b, c)) == True{} : Bool}
def less_that_sum_by_right(a, b, c, less):
  match a b:
    case 0n 0n: F.absurd_boolean({Nat.is_lt(0n, c) == True{} : Bool}, less)
    case 0n 1n+k: {==}
    case 1n+j 0n: F.absurd_boolean({Nat.is_lt(1n+j, c) == True{} : Bool}, less)
    case 1n+j 1n+k: less_that_sum_by_right(j, k, c, less)

def final_in_prefix(+before: List<&2, Q.Frame>, +later: List<&2, Q.Frame>,
  +r: P.Request, +ctx: D.Context, +w: D.State, +ts: List<&2, S.OperationEvent>, +proposal: S.Response, +end: Nat,
  index: &i: Nat -> {Q.query(before, i) == Some{Q.Evaluated{r, ctx, S.Final{w, ts, proposal}}} : Maybe<&2, Q.Frame>}) ->
  &u: Nat -> L.E<{Nat.is_lt(u, Nat.add(Q.size(before), end)) == True{} : Bool},
    {Q.query(Q.concatenate(before, later), u) == Some{Q.Evaluated{r, ctx, S.Final{w, ts, proposal}}} : Maybe<&2, Q.Frame>}>:
  match index:
    case (+i, query_result):
      F.combined_pair((&u: Nat -> L.E<{Nat.is_lt(u, Nat.add(Q.size(before), end)) == True{} : Bool},
          {Q.query(Q.concatenate(before, later), u) == Some{Q.Evaluated{r, ctx, S.Final{w, ts, proposal}}} : Maybe<&2, Q.Frame>}>),
        {Q.query(before, i) == Some{Q.Evaluated{r, ctx, S.Final{w, ts, proposal}}} : Maybe<&2, Q.Frame>},
        {Q.query(before, i) == Some{Q.Evaluated{r, ctx, S.Final{w, ts, proposal}}} : Maybe<&2, Q.Frame>},
        Call.duplicate_equality(Maybe<&2, Q.Frame>, Q.query(before, i), Some{Q.Evaluated{r, ctx, S.Final{w, ts, proposal}}}, query_result),
        limit => fact => (i, L.Both{
          less_that_sum_by_right(i, Q.size(before), end, Q.position_present_inside(before, i, Q.Evaluated{r, ctx, S.Final{w, ts, proposal}}, limit)),
          Q.query_prefix(before, later, i, Q.Evaluated{r, ctx, S.Final{w, ts, proposal}}, fact)}))

def response_final_combined_evaluation(~source: Source.Source, -a: I.Environment, -k: String, -x: I.Scenario,
  +before: List<&2, Q.Frame>, +later: List<&2, Q.Frame>, +end: Nat, +req: P.Request,
  +ctx: D.Context, +origin: Source.JudgmentSyntactic, +w: D.State, +ts: List<&2, S.OperationEvent>, +proposal: S.Response,
  -response: S.Response, finalized: {R.finalize(proposal, I.configuration(x), w) == response : S.Response},
  index: &u: Nat -> L.E<{Nat.is_lt(u, Nat.add(Q.size(before), end)) == True{} : Bool},
    {Q.query(Q.concatenate(before, later), u) == Some{Q.Evaluated{req, ctx, S.Final{w, ts, proposal}}} : Maybe<&2, Q.Frame>}>,
  introduce: @u: Nat -> {Q.query(Q.concatenate(before, later), u) == Some{Q.Evaluated{req, ctx, S.Final{w, ts, proposal}}} : Maybe<&2, Q.Frame>} ->
    I.Happens(a, k, x, u, I.Evaluated{req, ctx, Source.program(source, origin), S.Final{w, ts, proposal}})) ->
  I.ResponseOfProgram(a, k, x, Nat.add(Q.size(before), end), response, w):
  match index:
    case (+u, L.Both{order, query_result}):
      (req, ctx, Source.program(source, origin), ts, proposal, L.Both{(u, L.Both{order, introduce(u, query_result)}), finalized})

law response_final_has_cause_in_evaluation_real:
  for ~source: Source.Source
  for -a: I.Environment
  for -k: String
  for -x: I.Scenario
  for +before: List<&2, Q.Frame>
  for +later: List<&2, Q.Frame>
  for +end: Nat
  for +req: P.Request
  for +ctx: D.Context
  for +origin: Source.JudgmentSyntactic
  for +w: D.State
  for +ts: List<&2, S.OperationEvent>
  for +proposal: S.Response
  for -response: S.Response
  for finalized: {R.finalize(proposal, I.configuration(x), w) == response : S.Response}
  for index: &i: Nat -> {Q.query(before, i) == Some{Q.Evaluated{req, ctx, S.Final{w, ts, proposal}}} : Maybe<&2, Q.Frame>}
  for introduce: @u: Nat -> {Q.query(Q.concatenate(before, later), u) == Some{Q.Evaluated{req, ctx, S.Final{w, ts, proposal}}} : Maybe<&2, Q.Frame>} ->
    I.Happens(a, k, x, u, I.Evaluated{req, ctx, Source.program(source, origin), S.Final{w, ts, proposal}})
  I.ResponseOfProgram(a, k, x, Nat.add(Q.size(before), end), response, w)
def response_final_has_cause_in_evaluation_real(source, a, k, x, before, later, end, req, ctx, origin, w, ts, proposal, response, finalized, index, introduce):
  response_final_combined_evaluation(source, a, k, x, before, later, end, req, ctx, origin, w, ts, proposal, response, finalized,
    final_in_prefix(before, later, req, ctx, w, ts, proposal, end, index), introduce)

# Complete delivery: actual milestones, previous preparation and exclusion of partial delivery.
def before_of_delivery(+before: List<&2, Q.Frame>, +s: D.State, +r: S.Response,
  +bs: List<&2, U32>, +closes: Bool) -> List<&2, Q.Frame>:
  Q.concatenate(before, Con{Q.Prepared{r, bs}, Q.concatenate(H.render_publication(r, s), [Q.Completed{r, s, closes}])})

law separate_delivery:
  for +before: List<&2, Q.Frame>
  for +s: D.State
  for +r: S.Response
  for +bs: List<&2, U32>
  for +closes: Bool
  for +delivery: H.Delivery
  {Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closes, delivery)) ==
    Q.concatenate(before_of_delivery(before, s, r, bs, closes), H.render_delivery(s, bs, closes, delivery)) : List<&2, Q.Frame>}
def separate_delivery(before, s, r, bs, closes, delivery):
  Equal.sym(List<&2, Q.Frame>,
    Q.concatenate(before_of_delivery(before, s, r, bs, closes), H.render_delivery(s, bs, closes, delivery)),
    Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closes, delivery)),
    Equal.trans(List<&2, Q.Frame>,
      Q.concatenate(before_of_delivery(before, s, r, bs, closes), H.render_delivery(s, bs, closes, delivery)),
      Q.concatenate(before, Q.concatenate(Con{Q.Prepared{r, bs}, Q.concatenate(H.render_publication(r, s), [Q.Completed{r, s, closes}])}, H.render_delivery(s, bs, closes, delivery))),
      Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closes, delivery)),
      Q.concatenate_assoc(before, Con{Q.Prepared{r, bs}, Q.concatenate(H.render_publication(r, s), [Q.Completed{r, s, closes}])}, H.render_delivery(s, bs, closes, delivery)),
      Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, rest => Q.concatenate(before, Con{Q.Prepared{r, bs}, rest}),
        Q.concatenate(Q.concatenate(H.render_publication(r, s), [Q.Completed{r, s, closes}]), H.render_delivery(s, bs, closes, delivery)),
        Q.concatenate(H.render_publication(r, s), Con{Q.Completed{r, s, closes}, H.render_delivery(s, bs, closes, delivery)}),
        Q.concatenate_assoc(H.render_publication(r, s), [Q.Completed{r, s, closes}], H.render_delivery(s, bs, closes, delivery)))))

def publication_without_mark(+kind: Phases.FrameKind, r: S.Response, +s: D.State,
  negative: {Phases.of_that_kind(kind, Q.Published{s}) == False{} : Bool}) ->
  {Phases.absent(kind, H.render_publication(r, s)) == True{} : Bool}:
  match r:
    case S.Response{S.Success{}, v}:
      F.and_boolean_intro(Bool.not(Phases.of_that_kind(kind, Q.Published{s})), True{},
        Equal.cong(Bool, Bool, Bool.not, Phases.of_that_kind(kind, Q.Published{s}), False{}, negative), {==})
    case S.Response{S.Refusal{}, v}: {==}
    case S.Response{S.Input{}, v}: {==}
    case S.Response{S.Authentication{}, v}: {==}
    case S.Response{S.Certificate{}, v}: {==}
    case S.Response{S.DataError{}, v}: {==}
    case S.Response{S.Limit{}, v}: {==}
    case S.Response{S.Failure{}, v}: {==}

def before_of_delivery_without_mark(+kind: Phases.FrameKind, +before: List<&2, Q.Frame>, +s: D.State,
  +r: S.Response, +bs: List<&2, U32>, +closes: Bool,
  without: {Phases.absent(kind, before) == True{} : Bool},
  preparation: {Phases.of_that_kind(kind, Q.Prepared{r, bs}) == False{} : Bool},
  publication: {Phases.of_that_kind(kind, Q.Published{s}) == False{} : Bool},
  conclusion: {Phases.of_that_kind(kind, Q.Completed{r, s, closes}) == False{} : Bool}) ->
  {Phases.absent(kind, before_of_delivery(before, s, r, bs, closes)) == True{} : Bool}:
  Phases.concatenate_absence(kind, before, Con{Q.Prepared{r, bs}, Q.concatenate(H.render_publication(r, s), [Q.Completed{r, s, closes}])}, without,
    F.and_boolean_intro(Bool.not(Phases.of_that_kind(kind, Q.Prepared{r, bs})),
      Phases.absent(kind, Q.concatenate(H.render_publication(r, s), [Q.Completed{r, s, closes}])),
      Equal.cong(Bool, Bool, Bool.not, Phases.of_that_kind(kind, Q.Prepared{r, bs}), False{}, preparation),
      Phases.concatenate_absence(kind, H.render_publication(r, s), [Q.Completed{r, s, closes}], publication_without_mark(kind, r, s, publication),
        F.and_boolean_intro(Bool.not(Phases.of_that_kind(kind, Q.Completed{r, s, closes})), True{},
          Equal.cong(Bool, Bool, Bool.not, Phases.of_that_kind(kind, Q.Completed{r, s, closes}), False{}, conclusion), {==}))))

def delivery_complete_located(+before: List<&2, Q.Frame>, +s: D.State, +r: S.Response,
  +bs: List<&2, U32>, +closure: Bool, +next: Bool, +t: Nat, +q: Q.Frame,
  without: {Phases.absent(Phases.Complete{}, before) == True{} : Bool},
  target: {Phases.of_that_kind(Phases.Complete{}, q) == True{} : Bool},
  query_result: {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next})), t) == Some{q} : Maybe<&2, Q.Frame>}) ->
  L.E<{t == Q.size(before_of_delivery(before, s, r, bs, closure)) : Nat}, {q == Q.Delivered{bs} : Q.Frame}>:
  Phases.mark_unique_between_parts_absent(Phases.Complete{}, before_of_delivery(before, s, r, bs, closure), H.later_delivery(closure, s, next), Q.Delivered{bs}, t, q,
    before_of_delivery_without_mark(Phases.Complete{}, before, s, r, bs, closure, without, {==}, {==}, {==}),
    Phases.later_delivery_without_macros(Phases.Complete{}, closure, s, next), target,
    (%separate_delivery(before, s, r, bs, closure, H.Complete{next}) :
      {Q.query(_, t) == Some{q} : Maybe<&2, Q.Frame>} query_result))

def bytes_delivered(q: Q.Frame) -> Maybe<&2, List<&2, U32>>:
  match q:
    case Q.Delivered{bs}: Some{bs}
    case _: None{}

def delivery_located_compares(+before: List<&2, Q.Frame>, +s: D.State, +r: S.Response, +bs: List<&2, U32>, +closure: Bool,
  -u: Nat, -t: Nat, +other: List<&2, U32>, canonical: {t == Q.size(before_of_delivery(before, s, r, bs, closure)) : Nat},
  local: L.E<{u == Q.size(before_of_delivery(before, s, r, bs, closure)) : Nat}, {Q.Delivered{other} == Q.Delivered{bs} : Q.Frame}>) ->
  L.E<{u == t : Nat}, {other == bs : List<&2, U32>}>:
  match local:
    case L.Both{pos, frame}:
      L.Both{Equal.trans(Nat, u, Q.size(before_of_delivery(before, s, r, bs, closure)), t, pos,
        Equal.sym(Nat, t, Q.size(before_of_delivery(before, s, r, bs, closure)), canonical)),
        F.some_injective(List<&2, U32>, other, bs, Equal.cong(Q.Frame, Maybe<&2, List<&2, U32>>, bytes_delivered, Q.Delivered{other}, Q.Delivered{bs}, frame))}

def end_complete_without_interruption(+before: List<&2, Q.Frame>, +s: D.State, +r: S.Response,
  +bs: List<&2, U32>, +closure: Bool, +next: Bool, without: {Phases.absent(Phases.Interrupted{}, before) == True{} : Bool}) ->
  {Phases.absent(Phases.Interrupted{}, Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next}))) == True{} : Bool}:
  %Equal.sym(List<&2, Q.Frame>, Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next})),
    Q.concatenate(before_of_delivery(before, s, r, bs, closure), H.render_delivery(s, bs, closure, H.Complete{next})),
    separate_delivery(before, s, r, bs, closure, H.Complete{next})) : {Phases.absent(Phases.Interrupted{}, _) == True{} : Bool}
  Phases.concatenate_absence(Phases.Interrupted{}, before_of_delivery(before, s, r, bs, closure), H.render_delivery(s, bs, closure, H.Complete{next}),
    before_of_delivery_without_mark(Phases.Interrupted{}, before, s, r, bs, closure, without, {==}, {==}, {==}),
    Phases.delivery_complete_never_broken(s, bs, closure, next))

def position_of_delivery_complete(+before: List<&2, Q.Frame>, +s: D.State, +r: S.Response, +bs: List<&2, U32>, +closure: Bool,
  +next: Bool, +t: Nat, without: {Phases.absent(Phases.Complete{}, before) == True{} : Bool},
  query_result: {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next})), t) == Some{Q.Delivered{bs}} : Maybe<&2, Q.Frame>}) ->
  {t == Q.size(before_of_delivery(before, s, r, bs, closure)) : Nat}:
  L.and_left({t == Q.size(before_of_delivery(before, s, r, bs, closure)) : Nat}, {Q.Delivered{bs} == Q.Delivered{bs} : Q.Frame},
    delivery_complete_located(before, s, r, bs, closure, next, t, Q.Delivered{bs}, without, {==}, query_result))

def delivery_complete_unique_real(-a: I.Environment, -k: String, -x: I.Scenario, +before: List<&2, Q.Frame>,
  +s: D.State, +r: S.Response, +bs: List<&2, U32>, +closure: Bool, +next: Bool, -t: Nat,
  canonical: {t == Q.size(before_of_delivery(before, s, r, bs, closure)) : Nat},
  without_complete: {Phases.absent(Phases.Complete{}, before) == True{} : Bool},
  without_interrupted: {Phases.absent(Phases.Interrupted{}, before) == True{} : Bool},
  complete: @u: Nat -> @other: List<&2, U32> -> I.Happens(a, k, x, u, I.DeliveredEverything{other}) ->
    {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next})), u) == Some{Q.Delivered{other}} : Maybe<&2, Q.Frame>},
  interrupted: @u: Nat -> @prefix: List<&2, U32> -> I.Happens(a, k, x, u, I.DeliveryInterrupted{prefix}) ->
    {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next})), u) == Some{Q.Interrupted{prefix}} : Maybe<&2, Q.Frame>}) ->
  K.DeliveryCompleteUnique(a, k, x, t, bs):
  L.Both{+u => +other => fact => delivery_located_compares(before, s, r, bs, closure, u, t, other, canonical,
      delivery_complete_located(before, s, r, bs, closure, next, u, Q.Delivered{other}, without_complete, {==}, complete(u, other, fact))),
    +u => +prefix => fact => Phases.absent_excludes_query(Phases.Interrupted{},
      Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next})), u, Q.Interrupted{prefix},
      end_complete_without_interruption(before, s, r, bs, closure, next, without_interrupted), {==}, interrupted(u, prefix, fact))}

def local_conclusion(+s: D.State, +r: S.Response, +bs: List<&2, U32>) -> Nat:
  Q.size(Con{Q.Prepared{r, bs}, H.render_publication(r, s)})

def index_delivery(+before: List<&2, Q.Frame>, +s: D.State, +r: S.Response, +bs: List<&2, U32>) -> Nat:
  Nat.add(Q.size(before), Succ{local_conclusion(s, r, bs)})

def points_complete(+before: List<&2, Q.Frame>, +s: D.State, +r: S.Response, +bs: List<&2, U32>, +closure: Bool, +next: Bool) ->
  L.E<{Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next})), Nat.add(Q.size(before), local_conclusion(s, r, bs))) == Some{Q.Completed{r, s, closure}} : Maybe<&2, Q.Frame>},
    {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next})), index_delivery(before, s, r, bs)) == Some{Q.Delivered{bs}} : Maybe<&2, Q.Frame>}>:
  F.combined_pair(
    L.E<{Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next})), Nat.add(Q.size(before), local_conclusion(s, r, bs))) == Some{Q.Completed{r, s, closure}} : Maybe<&2, Q.Frame>},
      {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next})), index_delivery(before, s, r, bs)) == Some{Q.Delivered{bs}} : Maybe<&2, Q.Frame>}>,
    {Q.query(H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next}), local_conclusion(s, r, bs)) == Some{Q.Completed{r, s, closure}} : Maybe<&2, Q.Frame>},
    {Q.query(H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next}), Succ{local_conclusion(s, r, bs)}) == Some{Q.Delivered{bs}} : Maybe<&2, Q.Frame>},
    Q.two_frames_after_prefix(Con{Q.Prepared{r, bs}, H.render_publication(r, s)}, H.later_delivery(closure, s, next), Q.Completed{r, s, closure}, Q.Delivered{bs}),
    conclusion => delivery => L.Both{
      Equal.trans(Maybe<&2, Q.Frame>, Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next})), Nat.add(Q.size(before), local_conclusion(s, r, bs))),
        Q.query(H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next}), local_conclusion(s, r, bs)), Some{Q.Completed{r, s, closure}},
        Q.query_after_prefix(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next}), local_conclusion(s, r, bs)), conclusion),
      Equal.trans(Maybe<&2, Q.Frame>, Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next})), index_delivery(before, s, r, bs)),
        Q.query(H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next}), Succ{local_conclusion(s, r, bs)}), Some{Q.Delivered{bs}},
        Q.query_after_prefix(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next}), Succ{local_conclusion(s, r, bs)}), delivery)})

def preparation_in_end_complete(+before: List<&2, Q.Frame>, +s: D.State, +r: S.Response, +bs: List<&2, U32>, +closure: Bool, +next: Bool) ->
  {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next})), Nat.add(Q.size(before), 0n)) == Some{Q.Prepared{r, bs}} : Maybe<&2, Q.Frame>}:
  Q.query_after_prefix(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next}), 0n)

def position_complete_canonical(+before: List<&2, Q.Frame>, +s: D.State, +r: S.Response, +bs: List<&2, U32>, +closure: Bool, +next: Bool,
  without: {Phases.absent(Phases.Complete{}, before) == True{} : Bool}) ->
  {index_delivery(before, s, r, bs) == Q.size(before_of_delivery(before, s, r, bs, closure)) : Nat}:
  position_of_delivery_complete(before, s, r, bs, closure, next, index_delivery(before, s, r, bs), without,
    L.and_right(
      {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next})), Nat.add(Q.size(before), local_conclusion(s, r, bs))) == Some{Q.Completed{r, s, closure}} : Maybe<&2, Q.Frame>},
      {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next})), index_delivery(before, s, r, bs)) == Some{Q.Delivered{bs}} : Maybe<&2, Q.Frame>}, points_complete(before, s, r, bs, closure, next)))

def uniqueness_complete_canonical(-a: I.Environment, -k: String, -x: I.Scenario,
  +before: List<&2, Q.Frame>, +s: D.State, +r: S.Response, +bs: List<&2, U32>, +closure: Bool, +next: Bool,
  without_complete: {Phases.absent(Phases.Complete{}, before) == True{} : Bool},
  without_interrupted: {Phases.absent(Phases.Interrupted{}, before) == True{} : Bool},
  complete: @u: Nat -> @other: List<&2, U32> -> I.Happens(a, k, x, u, I.DeliveredEverything{other}) ->
    {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next})), u) == Some{Q.Delivered{other}} : Maybe<&2, Q.Frame>},
  interrupted: @u: Nat -> @prefix: List<&2, U32> -> I.Happens(a, k, x, u, I.DeliveryInterrupted{prefix}) ->
    {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next})), u) == Some{Q.Interrupted{prefix}} : Maybe<&2, Q.Frame>}) ->
  K.DeliveryCompleteUnique(a, k, x, index_delivery(before, s, r, bs), bs):
  F.combined_pair(K.DeliveryCompleteUnique(a, k, x, index_delivery(before, s, r, bs), bs),
    {Phases.absent(Phases.Complete{}, before) == True{} : Bool}, {Phases.absent(Phases.Complete{}, before) == True{} : Bool},
    Call.duplicate_equality(Bool, Phases.absent(Phases.Complete{}, before), True{}, without_complete),
    index => other => delivery_complete_unique_real(a, k, x, before, s, r, bs, closure, next, index_delivery(before, s, r, bs),
      position_complete_canonical(before, s, r, bs, closure, next, index), other, without_interrupted, complete, interrupted))

law delivery_complete_canonical_obeys_rule7:
  for -a: I.Environment
  for -k: String
  for -x: I.Scenario
  for +before: List<&2, Q.Frame>
  for +s: D.State
  for +r: S.Response
  for +bs: List<&2, U32>
  for +closure: Bool
  for +next: Bool
  for without_complete: {Phases.absent(Phases.Complete{}, before) == True{} : Bool}
  for without_interrupted: {Phases.absent(Phases.Interrupted{}, before) == True{} : Bool}
  for prepare: @u: Nat -> @rp: S.Response -> @bytes: List<&2, U32> ->
    {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next})), u) == Some{Q.Prepared{rp, bytes}} : Maybe<&2, Q.Frame>} ->
    I.Happens(a, k, x, u, I.Prepared{rp, bytes})
  for conclude: @u: Nat -> @rp: S.Response -> @w: D.State -> @closes: Bool ->
    {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next})), u) == Some{Q.Completed{rp, w, closes}} : Maybe<&2, Q.Frame>} ->
    I.Happens(a, k, x, u, I.Concluded{rp, w, closes})
  for complete: @u: Nat -> @other: List<&2, U32> -> I.Happens(a, k, x, u, I.DeliveredEverything{other}) ->
    {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next})), u) == Some{Q.Delivered{other}} : Maybe<&2, Q.Frame>}
  for interrupted: @u: Nat -> @prefix: List<&2, U32> -> I.Happens(a, k, x, u, I.DeliveryInterrupted{prefix}) ->
    {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next})), u) == Some{Q.Interrupted{prefix}} : Maybe<&2, Q.Frame>}
  K.Rule7(I.DeliveredEverything{bs}, a, k, x, index_delivery(before, s, r, bs))
def delivery_complete_canonical_obeys_rule7(a, k, x, before, s, r, bs, closure, next, without_complete, without_interrupted,
  prepare, conclude, complete, interrupted):
  (r, s, closure, L.Both{
    (Nat.add(Q.size(before), local_conclusion(s, r, bs)), L.Both{
      Q.order_shifted(Q.size(before), local_conclusion(s, r, bs), Succ{local_conclusion(s, r, bs)}, Exec.less_successor(local_conclusion(s, r, bs))),
      conclude(Nat.add(Q.size(before), local_conclusion(s, r, bs)), r, s, closure,
        L.and_left(
          {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next})), Nat.add(Q.size(before), local_conclusion(s, r, bs))) == Some{Q.Completed{r, s, closure}} : Maybe<&2, Q.Frame>},
          {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next})), index_delivery(before, s, r, bs)) == Some{Q.Delivered{bs}} : Maybe<&2, Q.Frame>}, points_complete(before, s, r, bs, closure, next)))}),
    L.Both{(Nat.add(Q.size(before), 0n), L.Both{
        Q.order_shifted(Q.size(before), 0n, Succ{local_conclusion(s, r, bs)}, {==}),
        prepare(Nat.add(Q.size(before), 0n), r, bs, preparation_in_end_complete(before, s, r, bs, closure, next))}),
      uniqueness_complete_canonical(a, k, x, before, s, r, bs, closure, next, without_complete, without_interrupted, complete, interrupted)}})

def transport_delivery7(-a: I.Environment, -k: String, -x: I.Scenario, +before: List<&2, Q.Frame>,
  +s: D.State, +r: S.Response, +bs: List<&2, U32>, -t: Nat, +other: List<&2, U32>,
  equal: L.E<{t == index_delivery(before, s, r, bs) : Nat}, {other == bs : List<&2, U32>}>,
  canonical: K.Rule7(I.DeliveredEverything{bs}, a, k, x, index_delivery(before, s, r, bs))) ->
  K.Rule7(I.DeliveredEverything{other}, a, k, x, t):
  match equal:
    case L.Both{pos, bytes}:
      %Equal.sym(Nat, t, index_delivery(before, s, r, bs), pos) : K.Rule7(I.DeliveredEverything{other}, a, k, x, _)
      %Equal.sym(List<&2, U32>, other, bs, bytes) : K.Rule7(I.DeliveredEverything{_}, a, k, x, index_delivery(before, s, r, bs))
      canonical

law delivery_complete_reflected_obeys_rule7:
  for -a: I.Environment
  for -k: String
  for -x: I.Scenario
  for +before: List<&2, Q.Frame>
  for +s: D.State
  for +r: S.Response
  for +bs: List<&2, U32>
  for +closure: Bool
  for +next: Bool
  for +t: Nat
  for +other: List<&2, U32>
  for query_result: {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next})), t) == Some{Q.Delivered{other}} : Maybe<&2, Q.Frame>}
  for without_complete: {Phases.absent(Phases.Complete{}, before) == True{} : Bool}
  for without_interrupted: {Phases.absent(Phases.Interrupted{}, before) == True{} : Bool}
  for prepare: @u: Nat -> @rp: S.Response -> @bytes: List<&2, U32> ->
    {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next})), u) == Some{Q.Prepared{rp, bytes}} : Maybe<&2, Q.Frame>} ->
    I.Happens(a, k, x, u, I.Prepared{rp, bytes})
  for conclude: @u: Nat -> @rp: S.Response -> @w: D.State -> @closes: Bool ->
    {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next})), u) == Some{Q.Completed{rp, w, closes}} : Maybe<&2, Q.Frame>} ->
    I.Happens(a, k, x, u, I.Concluded{rp, w, closes})
  for complete: @u: Nat -> @bytes: List<&2, U32> -> I.Happens(a, k, x, u, I.DeliveredEverything{bytes}) ->
    {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next})), u) == Some{Q.Delivered{bytes}} : Maybe<&2, Q.Frame>}
  for interrupted: @u: Nat -> @prefix: List<&2, U32> -> I.Happens(a, k, x, u, I.DeliveryInterrupted{prefix}) ->
    {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next})), u) == Some{Q.Interrupted{prefix}} : Maybe<&2, Q.Frame>}
  K.Rule7(I.DeliveredEverything{other}, a, k, x, t)
def delivery_complete_reflected_obeys_rule7(a, k, x, before, s, r, bs, closure, next, t, other, query_result, without_complete, without_interrupted,
  prepare, conclude, complete, interrupted):
  F.combined_pair(K.Rule7(I.DeliveredEverything{other}, a, k, x, t),
    {Phases.absent(Phases.Complete{}, before) == True{} : Bool}, {Phases.absent(Phases.Complete{}, before) == True{} : Bool},
    Call.duplicate_equality(Bool, Phases.absent(Phases.Complete{}, before), True{}, without_complete),
    current => rest => F.combined_pair(K.Rule7(I.DeliveredEverything{other}, a, k, x, t),
      {Phases.absent(Phases.Complete{}, before) == True{} : Bool}, {Phases.absent(Phases.Complete{}, before) == True{} : Bool},
      Call.duplicate_equality(Bool, Phases.absent(Phases.Complete{}, before), True{}, rest),
      pos => canonical => transport_delivery7(a, k, x, before, s, r, bs, t, other,
        delivery_located_compares(before, s, r, bs, closure, t, index_delivery(before, s, r, bs), other,
          position_complete_canonical(before, s, r, bs, closure, next, pos),
          delivery_complete_located(before, s, r, bs, closure, next, t, Q.Delivered{other}, current, {==}, query_result)),
        delivery_complete_canonical_obeys_rule7(a, k, x, before, s, r, bs, closure, next, canonical, without_interrupted, prepare, conclude, complete, interrupted))))

# Publication derives validity from history and response from actual evaluation.
def OriginOfSource(~source: Source.Source, -c: S.Configuration, -s: D.State, +origin: Source.JudgmentSyntactic,
  record: History.Record) -> Type:
  match record:
    case History.Record{req, ctx, n, w, ts, proposal, prepared}:
      L.E<R.Certifies(c, I.code(req), Source.program(source, origin), ctx, I.arguments(req)),
        L.E<{D.authenticate(s, I.credential(req)) == Some{ctx} : Maybe<&2, D.Context>},
          L.E<{N.traverse(n, N.start(Source.program(source, origin), ctx, I.arguments(req), s), S.schema(c)) == S.Final{w, ts, proposal} : S.Trace},
            {N.prepare(N.Stopped{w, ts, proposal}, c) == Some{prepared} : Maybe<&2, N.Prepared>}>>>

def history_of_source(~source: Source.Source, -c: S.Configuration, -s: D.State, +origin: Source.JudgmentSyntactic,
  +record: History.Record, proof: OriginOfSource(source, c, s, origin, record)) -> History.Origin(c, s, record):
  match record:
    case History.Record{req, ctx, n, w, ts, proposal, prepared}:
      (Source.program(source, origin), proof)

def transport_publication6(-a: I.Environment, -k: String, -x: I.Scenario, +before: List<&2, Q.Frame>,
  +w: D.State, -t: Nat, +published: D.State,
  equal: L.E<{t == Nat.add(Q.size(before), 1n) : Nat}, {published == w : D.State}>,
  canonical: K.Rule6(I.Published{w}, a, k, x, Nat.add(Q.size(before), 1n))) -> K.Rule6(I.Published{published}, a, k, x, t):
  match equal:
    case L.Both{pos, state}:
      %Equal.sym(Nat, t, Nat.add(Q.size(before), 1n), pos) : K.Rule6(I.Published{published}, a, k, x, _)
      %Equal.sym(D.State, published, w, state) : K.Rule6(I.Published{_}, a, k, x, Nat.add(Q.size(before), 1n))
      canonical

def proposal_negative_fabricates_status_host(~source: Source.Source, ~c: S.Configuration, +s: D.State,
  +req: P.Request, +ctx: D.Context, +origin: Source.JudgmentSyntactic, +n: Nat,
  +w: D.State, +ts: List<&2, S.OperationEvent>, +proposal: S.Response,
  result: {N.traverse(n, N.start(Source.program(source, origin), ctx, I.arguments(req), s), S.schema(c)) == S.Final{w, ts, proposal} : S.Trace}) ->
  Phases.OfCode(proposal):
  %result : Phases.TraceOfCode(_)
  Phases.execution_trace_negative_fabricates_status_of_host(n, N.start(Source.program(source, origin), ctx, I.arguments(req), s), S.schema(c), Unit{})

def response_prepared_of_faithful(~c: S.Configuration, +w: D.State, +ts: List<&2, S.OperationEvent>,
  +proposal: S.Response, +r: S.Response, +bs: List<&2, U32>,
  faithful: Preparation.Faithful(w, ts, R.finalize(proposal, c, w), N.Prepared{w, ts, r, bs})) ->
  {R.finalize(proposal, c, w) == r : S.Response}:
  match faithful:
    case L.Both{equal, message}:
      Equal.sym(S.Response, r, R.finalize(proposal, c, w), Equal.cong(N.Prepared, S.Response, U.response,
        N.Prepared{w, ts, r, bs}, N.Prepared{w, ts, R.finalize(proposal, c, w), bs}, equal))

def response_prepared_and_finalization(~c: S.Configuration, +w: D.State, +ts: List<&2, S.OperationEvent>,
  +proposal: S.Response, +r: S.Response, +bs: List<&2, U32>,
  obtained: {N.prepare(N.Stopped{w, ts, proposal}, c) == Some{N.Prepared{w, ts, r, bs}} : Maybe<&2, N.Prepared>}) ->
  {R.finalize(proposal, c, w) == r : S.Response}:
  response_prepared_of_faithful(c, w, ts, proposal, r, bs,
    Preparation.prepare_preserves_response_state_events_and_bytes(N.Stopped{w, ts, proposal}, c, N.Prepared{w, ts, r, bs}, obtained))

def data_prepared_of_scenario(~c: S.Configuration, -x: I.Scenario, +w: D.State, +ts: List<&2, S.OperationEvent>,
  +proposal: S.Response, +r: S.Response, +bs: List<&2, U32>,
  obtained: {N.prepare(N.Stopped{w, ts, proposal}, c) == Some{N.Prepared{w, ts, r, bs}} : Maybe<&2, N.Prepared>},
  configuration: {I.configuration(x) == c : S.Configuration}, is_valid: {R.configuration_is_valid(c) == True{} : Bool}) ->
  Phases.DataPrepared(I.configuration(x), N.Prepared{w, ts, r, bs}):
  %Equal.sym(S.Configuration, I.configuration(x), c, configuration) : Phases.DataPrepared(_, N.Prepared{w, ts, r, bs})
  Phases.prepare_real_guarantees_payload_message_and_size(c, w, ts, proposal, N.Prepared{w, ts, r, bs}, obtained,
    Preparation.limits_of_configuration(c, is_valid))

def cause_of_preparation(~source: Source.Source, ~c: S.Configuration, -a: I.Environment, -k: String, -x: I.Scenario,
  +before: List<&2, Q.Frame>, +later: List<&2, Q.Frame>, +req: P.Request, +ctx: D.Context,
  +origin: Source.JudgmentSyntactic, +w: D.State, +ts: List<&2, S.OperationEvent>, +proposal: S.Response, +r: S.Response,
  configuration: {I.configuration(x) == c : S.Configuration}, finalized: {R.finalize(proposal, c, w) == r : S.Response},
  of_code: Phases.OfCode(proposal),
  index: &i: Nat -> {Q.query(before, i) == Some{Q.Evaluated{req, ctx, S.Final{w, ts, proposal}}} : Maybe<&2, Q.Frame>},
  evaluate: @u: Nat -> {Q.query(Q.concatenate(before, later), u) == Some{Q.Evaluated{req, ctx, S.Final{w, ts, proposal}}} : Maybe<&2, Q.Frame>} ->
    I.Happens(a, k, x, u, I.Evaluated{req, ctx, Source.program(source, origin), S.Final{w, ts, proposal}})) ->
  I.ResponseJustified(r, a, k, x, Nat.add(Q.size(before), 0n)):
  %finalized : I.ResponseJustified(_, a, k, x, Nat.add(Q.size(before), 0n))
  Phases.response_of_program_justifies_o_status_real(a, k, x, Nat.add(Q.size(before), 0n), R.finalize(proposal, c, w), w,
    Phases.finalize_only_appends_data_or_limit(proposal, c, w, of_code),
    response_final_has_cause_in_evaluation_real(source, a, k, x, before, later, 0n, req, ctx, origin, w, ts, proposal,
      R.finalize(proposal, c, w), Equal.cong(S.Configuration, S.Response, cfg => R.finalize(proposal, cfg, w),
        I.configuration(x), c, configuration), index, evaluate))

def combine_preparation(-a: I.Environment, -k: String, -x: I.Scenario, -t: Nat, -w: D.State, -ts: List<&2, S.OperationEvent>,
  +r: S.Response, +bs: List<&2, U32>, data: Phases.DataPrepared(I.configuration(x), N.Prepared{w, ts, r, bs}),
  cause: I.ResponseJustified(r, a, k, x, t)) -> K.Rule7(I.Prepared{r, bs}, a, k, x, t):
  match data:
    case L.Both{value, L.Both{message, size}}: L.Both{value, L.Both{message, L.Both{size, cause}}}

law preparation_of_program_obeys_rule7:
  for ~source: Source.Source
  for ~c: S.Configuration
  for -a: I.Environment
  for -k: String
  for -x: I.Scenario
  for +before: List<&2, Q.Frame>
  for +later: List<&2, Q.Frame>
  for +s: D.State
  for +req: P.Request
  for +ctx: D.Context
  for +origin: Source.JudgmentSyntactic
  for +n: Nat
  for +w: D.State
  for +ts: List<&2, S.OperationEvent>
  for +proposal: S.Response
  for +r: S.Response
  for +bs: List<&2, U32>
  for configuration: {I.configuration(x) == c : S.Configuration}
  for is_valid: {R.configuration_is_valid(c) == True{} : Bool}
  for obtained: {N.prepare(N.Stopped{w, ts, proposal}, c) == Some{N.Prepared{w, ts, r, bs}} : Maybe<&2, N.Prepared>}
  for result: {N.traverse(n, N.start(Source.program(source, origin), ctx, I.arguments(req), s), S.schema(c)) == S.Final{w, ts, proposal} : S.Trace}
  for index: &i: Nat -> {Q.query(before, i) == Some{Q.Evaluated{req, ctx, S.Final{w, ts, proposal}}} : Maybe<&2, Q.Frame>}
  for evaluate: @u: Nat -> {Q.query(Q.concatenate(before, later), u) == Some{Q.Evaluated{req, ctx, S.Final{w, ts, proposal}}} : Maybe<&2, Q.Frame>} ->
    I.Happens(a, k, x, u, I.Evaluated{req, ctx, Source.program(source, origin), S.Final{w, ts, proposal}})
  K.Rule7(I.Prepared{r, bs}, a, k, x, Nat.add(Q.size(before), 0n))
def preparation_of_program_obeys_rule7(source, c, a, k, x, before, later, s, req, ctx, origin, n, w, ts, proposal, r, bs,
  configuration, is_valid, obtained, result, index, evaluate):
  F.combined_pair(K.Rule7(I.Prepared{r, bs}, a, k, x, Nat.add(Q.size(before), 0n)),
    {I.configuration(x) == c : S.Configuration}, {I.configuration(x) == c : S.Configuration},
    Call.duplicate_equality(S.Configuration, I.configuration(x), c, configuration),
    data_cfg => cause_cfg => F.combined_pair(K.Rule7(I.Prepared{r, bs}, a, k, x, Nat.add(Q.size(before), 0n)),
      {N.prepare(N.Stopped{w, ts, proposal}, c) == Some{N.Prepared{w, ts, r, bs}} : Maybe<&2, N.Prepared>},
      {N.prepare(N.Stopped{w, ts, proposal}, c) == Some{N.Prepared{w, ts, r, bs}} : Maybe<&2, N.Prepared>},
      Call.duplicate_equality(Maybe<&2, N.Prepared>, N.prepare(N.Stopped{w, ts, proposal}, c), Some{N.Prepared{w, ts, r, bs}}, obtained),
      data => response => combine_preparation(a, k, x, Nat.add(Q.size(before), 0n), w, ts, r, bs,
        data_prepared_of_scenario(c, x, w, ts, proposal, r, bs, data, data_cfg, is_valid),
        cause_of_preparation(source, c, a, k, x, before, later, req, ctx, origin, w, ts, proposal, r, cause_cfg,
          response_prepared_and_finalization(c, w, ts, proposal, r, bs, response),
          proposal_negative_fabricates_status_host(source, c, s, req, ctx, origin, n, w, ts, proposal, result), index, evaluate))))

# Partial delivery preserves the actual written prefix and fabricates no complete delivery.
def delivery_partial_located(+before: List<&2, Q.Frame>, +s: D.State, +r: S.Response,
  +bs: List<&2, U32>, +closure: Bool, +prefix: List<&2, U32>, +t: Nat, +q: Q.Frame,
  without: {Phases.absent(Phases.Interrupted{}, before) == True{} : Bool},
  target: {Phases.of_that_kind(Phases.Interrupted{}, q) == True{} : Bool},
  query_result: {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix})), t) == Some{q} : Maybe<&2, Q.Frame>}) ->
  L.E<{t == Q.size(before_of_delivery(before, s, r, bs, closure)) : Nat}, {q == Q.Interrupted{prefix} : Q.Frame}>:
  Phases.mark_unique_between_parts_absent(Phases.Interrupted{}, before_of_delivery(before, s, r, bs, closure), [Q.Closed{}], Q.Interrupted{prefix}, t, q,
    before_of_delivery_without_mark(Phases.Interrupted{}, before, s, r, bs, closure, without, {==}, {==}, {==}), {==}, target,
    (%separate_delivery(before, s, r, bs, closure, H.Broken{prefix}) :
      {Q.query(_, t) == Some{q} : Maybe<&2, Q.Frame>} query_result))

def prefix_interrupted(q: Q.Frame) -> Maybe<&2, List<&2, U32>>:
  match q:
    case Q.Interrupted{bs}: Some{bs}
    case _: None{}

def position_partial_compares(+before: List<&2, Q.Frame>, +s: D.State, +r: S.Response, +bs: List<&2, U32>, +closure: Bool,
  +prefix: List<&2, U32>, -u: Nat, -t: Nat, +other: List<&2, U32>,
  canonical: {t == Q.size(before_of_delivery(before, s, r, bs, closure)) : Nat},
  local: L.E<{u == Q.size(before_of_delivery(before, s, r, bs, closure)) : Nat}, {Q.Interrupted{other} == Q.Interrupted{prefix} : Q.Frame}>) ->
  L.E<{u == t : Nat}, {other == prefix : List<&2, U32>}>:
  match local:
    case L.Both{pos, frame}:
      L.Both{Equal.trans(Nat, u, Q.size(before_of_delivery(before, s, r, bs, closure)), t, pos,
          Equal.sym(Nat, t, Q.size(before_of_delivery(before, s, r, bs, closure)), canonical)),
        F.some_injective(List<&2, U32>, other, prefix, Equal.cong(Q.Frame, Maybe<&2, List<&2, U32>>, prefix_interrupted, Q.Interrupted{other}, Q.Interrupted{prefix}, frame))}

def end_partial_without_complete(+before: List<&2, Q.Frame>, +s: D.State, +r: S.Response, +bs: List<&2, U32>, +closure: Bool,
  +prefix: List<&2, U32>, without: {Phases.absent(Phases.Complete{}, before) == True{} : Bool}) ->
  {Phases.absent(Phases.Complete{}, Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix}))) == True{} : Bool}:
  %Equal.sym(List<&2, Q.Frame>, Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix})),
    Q.concatenate(before_of_delivery(before, s, r, bs, closure), H.render_delivery(s, bs, closure, H.Broken{prefix})),
    separate_delivery(before, s, r, bs, closure, H.Broken{prefix})) : {Phases.absent(Phases.Complete{}, _) == True{} : Bool}
  Phases.concatenate_absence(Phases.Complete{}, before_of_delivery(before, s, r, bs, closure), H.render_delivery(s, bs, closure, H.Broken{prefix}),
    before_of_delivery_without_mark(Phases.Complete{}, before, s, r, bs, closure, without, {==}, {==}, {==}), {==})

def points_partial(+before: List<&2, Q.Frame>, +s: D.State, +r: S.Response, +bs: List<&2, U32>, +closure: Bool, +prefix: List<&2, U32>) ->
  L.E<{Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix})), Nat.add(Q.size(before), local_conclusion(s, r, bs))) == Some{Q.Completed{r, s, closure}} : Maybe<&2, Q.Frame>},
    {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix})), index_delivery(before, s, r, bs)) == Some{Q.Interrupted{prefix}} : Maybe<&2, Q.Frame>}>:
  F.combined_pair(
    L.E<{Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix})), Nat.add(Q.size(before), local_conclusion(s, r, bs))) == Some{Q.Completed{r, s, closure}} : Maybe<&2, Q.Frame>},
      {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix})), index_delivery(before, s, r, bs)) == Some{Q.Interrupted{prefix}} : Maybe<&2, Q.Frame>}>,
    {Q.query(H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix}), local_conclusion(s, r, bs)) == Some{Q.Completed{r, s, closure}} : Maybe<&2, Q.Frame>},
    {Q.query(H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix}), Succ{local_conclusion(s, r, bs)}) == Some{Q.Interrupted{prefix}} : Maybe<&2, Q.Frame>},
    Q.two_frames_after_prefix(Con{Q.Prepared{r, bs}, H.render_publication(r, s)}, [Q.Closed{}], Q.Completed{r, s, closure}, Q.Interrupted{prefix}),
    conclusion => delivery => L.Both{
      Equal.trans(Maybe<&2, Q.Frame>, Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix})), Nat.add(Q.size(before), local_conclusion(s, r, bs))),
        Q.query(H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix}), local_conclusion(s, r, bs)), Some{Q.Completed{r, s, closure}},
        Q.query_after_prefix(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix}), local_conclusion(s, r, bs)), conclusion),
      Equal.trans(Maybe<&2, Q.Frame>, Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix})), index_delivery(before, s, r, bs)),
        Q.query(H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix}), Succ{local_conclusion(s, r, bs)}), Some{Q.Interrupted{prefix}},
        Q.query_after_prefix(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix}), Succ{local_conclusion(s, r, bs)}), delivery)})

def partial_unique_real(-a: I.Environment, -k: String, -x: I.Scenario, +before: List<&2, Q.Frame>,
  +s: D.State, +r: S.Response, +bs: List<&2, U32>, +closure: Bool, +prefix: List<&2, U32>, -t: Nat,
  canonical: {t == Q.size(before_of_delivery(before, s, r, bs, closure)) : Nat},
  without_complete: {Phases.absent(Phases.Complete{}, before) == True{} : Bool},
  without_interrupted: {Phases.absent(Phases.Interrupted{}, before) == True{} : Bool},
  complete: @u: Nat -> @other: List<&2, U32> -> I.Happens(a, k, x, u, I.DeliveredEverything{other}) ->
    {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix})), u) == Some{Q.Delivered{other}} : Maybe<&2, Q.Frame>},
  interrupted: @u: Nat -> @other: List<&2, U32> -> I.Happens(a, k, x, u, I.DeliveryInterrupted{other}) ->
    {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix})), u) == Some{Q.Interrupted{other}} : Maybe<&2, Q.Frame>}) ->
  K.DeliveryInterruptedUnique(a, k, x, t, prefix):
  L.Both{+u => +other => fact => position_partial_compares(before, s, r, bs, closure, prefix, u, t, other, canonical,
      delivery_partial_located(before, s, r, bs, closure, prefix, u, Q.Interrupted{other}, without_interrupted, {==}, interrupted(u, other, fact))),
    +u => +other => fact => Phases.absent_excludes_query(Phases.Complete{},
      Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix})), u, Q.Delivered{other},
      end_partial_without_complete(before, s, r, bs, closure, prefix, without_complete), {==}, complete(u, other, fact))}

def position_partial_canonical(+before: List<&2, Q.Frame>, +s: D.State, +r: S.Response, +bs: List<&2, U32>, +closure: Bool,
  +prefix: List<&2, U32>, without: {Phases.absent(Phases.Interrupted{}, before) == True{} : Bool}) ->
  {index_delivery(before, s, r, bs) == Q.size(before_of_delivery(before, s, r, bs, closure)) : Nat}:
  L.and_left({index_delivery(before, s, r, bs) == Q.size(before_of_delivery(before, s, r, bs, closure)) : Nat}, {Q.Interrupted{prefix} == Q.Interrupted{prefix} : Q.Frame},
    delivery_partial_located(before, s, r, bs, closure, prefix, index_delivery(before, s, r, bs), Q.Interrupted{prefix}, without, {==},
      L.and_right(
        {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix})), Nat.add(Q.size(before), local_conclusion(s, r, bs))) == Some{Q.Completed{r, s, closure}} : Maybe<&2, Q.Frame>},
        {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix})), index_delivery(before, s, r, bs)) == Some{Q.Interrupted{prefix}} : Maybe<&2, Q.Frame>}, points_partial(before, s, r, bs, closure, prefix))))

law delivery_partial_canonical_obeys_rule7:
  for -a: I.Environment
  for -k: String
  for -x: I.Scenario
  for +before: List<&2, Q.Frame>
  for +s: D.State
  for +r: S.Response
  for +bs: List<&2, U32>
  for +closure: Bool
  for +prefix: List<&2, U32>
  for prefix_real: L.Prefix(U32, prefix, bs)
  for failed: I.FailureDeliveryReal(a, k, x, index_delivery(before, s, r, bs))
  for without_complete: {Phases.absent(Phases.Complete{}, before) == True{} : Bool}
  for without_interrupted: {Phases.absent(Phases.Interrupted{}, before) == True{} : Bool}
  for prepare: @u: Nat -> @rp: S.Response -> @bytes: List<&2, U32> ->
    {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix})), u) == Some{Q.Prepared{rp, bytes}} : Maybe<&2, Q.Frame>} -> I.Happens(a, k, x, u, I.Prepared{rp, bytes})
  for conclude: @u: Nat -> @rp: S.Response -> @w: D.State -> @closes: Bool ->
    {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix})), u) == Some{Q.Completed{rp, w, closes}} : Maybe<&2, Q.Frame>} -> I.Happens(a, k, x, u, I.Concluded{rp, w, closes})
  for complete: @u: Nat -> @other: List<&2, U32> -> I.Happens(a, k, x, u, I.DeliveredEverything{other}) ->
    {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix})), u) == Some{Q.Delivered{other}} : Maybe<&2, Q.Frame>}
  for interrupted: @u: Nat -> @other: List<&2, U32> -> I.Happens(a, k, x, u, I.DeliveryInterrupted{other}) ->
    {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix})), u) == Some{Q.Interrupted{other}} : Maybe<&2, Q.Frame>}
  K.Rule7(I.DeliveryInterrupted{prefix}, a, k, x, index_delivery(before, s, r, bs))
def delivery_partial_canonical_obeys_rule7(a, k, x, before, s, r, bs, closure, prefix, prefix_real, failed, without_complete, without_interrupted, prepare, conclude, complete, interrupted):
  F.combined_pair(K.Rule7(I.DeliveryInterrupted{prefix}, a, k, x, index_delivery(before, s, r, bs)),
    {Phases.absent(Phases.Interrupted{}, before) == True{} : Bool}, {Phases.absent(Phases.Interrupted{}, before) == True{} : Bool},
    Call.duplicate_equality(Bool, Phases.absent(Phases.Interrupted{}, before), True{}, without_interrupted),
    for_index => for_other =>
      (r, s, closure, bs, L.Both{
        (Nat.add(Q.size(before), local_conclusion(s, r, bs)), L.Both{
          Q.order_shifted(Q.size(before), local_conclusion(s, r, bs), Succ{local_conclusion(s, r, bs)}, Exec.less_successor(local_conclusion(s, r, bs))),
          conclude(Nat.add(Q.size(before), local_conclusion(s, r, bs)), r, s, closure,
            L.and_left(
              {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix})), Nat.add(Q.size(before), local_conclusion(s, r, bs))) == Some{Q.Completed{r, s, closure}} : Maybe<&2, Q.Frame>},
              {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix})), index_delivery(before, s, r, bs)) == Some{Q.Interrupted{prefix}} : Maybe<&2, Q.Frame>}, points_partial(before, s, r, bs, closure, prefix)))}),
        L.Both{(Nat.add(Q.size(before), 0n), L.Both{Q.order_shifted(Q.size(before), 0n, Succ{local_conclusion(s, r, bs)}, {==}),
            prepare(Nat.add(Q.size(before), 0n), r, bs, Q.query_after_prefix(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix}), 0n))}),
          L.Both{prefix_real, L.Both{partial_unique_real(a, k, x, before, s, r, bs, closure, prefix, index_delivery(before, s, r, bs),
            position_partial_canonical(before, s, r, bs, closure, prefix, for_index), without_complete, for_other, complete, interrupted), failed}}}}))

def transport_partial7(-a: I.Environment, -k: String, -x: I.Scenario, +before: List<&2, Q.Frame>,
  +s: D.State, +r: S.Response, +bs: List<&2, U32>, +prefix: List<&2, U32>, -t: Nat, +other: List<&2, U32>,
  equal: L.E<{t == index_delivery(before, s, r, bs) : Nat}, {other == prefix : List<&2, U32>}>,
  canonical: K.Rule7(I.DeliveryInterrupted{prefix}, a, k, x, index_delivery(before, s, r, bs))) ->
  K.Rule7(I.DeliveryInterrupted{other}, a, k, x, t):
  match equal:
    case L.Both{pos, bytes}:
      %Equal.sym(Nat, t, index_delivery(before, s, r, bs), pos) : K.Rule7(I.DeliveryInterrupted{other}, a, k, x, _)
      %Equal.sym(List<&2, U32>, other, prefix, bytes) : K.Rule7(I.DeliveryInterrupted{_}, a, k, x, index_delivery(before, s, r, bs))
      canonical

# The write receipt states only actual bytes and error; the route supplies the rest.
def summand_real_located(-a: I.Environment, -k: String, -x: I.Scenario, +before: List<&2, Q.Frame>,
  +s: D.State, +r: S.Response, +bs: List<&2, U32>, +prefix: List<&2, U32>, -t: Nat, +other: List<&2, U32>,
  equal: L.E<{t == index_delivery(before, s, r, bs) : Nat}, {other == prefix : List<&2, U32>}>,
  failed: I.FailureDeliveryReal(a, k, x, t),
  generate: I.FailureDeliveryReal(a, k, x, index_delivery(before, s, r, bs)) -> K.Rule7(I.DeliveryInterrupted{prefix}, a, k, x, index_delivery(before, s, r, bs))) ->
  K.Rule7(I.DeliveryInterrupted{other}, a, k, x, t):
  match equal:
    case L.Both{pos, data}:
      F.combined_pair(K.Rule7(I.DeliveryInterrupted{other}, a, k, x, t),
        {t == index_delivery(before, s, r, bs) : Nat}, {t == index_delivery(before, s, r, bs) : Nat},
        Call.duplicate_equality(Nat, t, index_delivery(before, s, r, bs), pos),
        for_kind => for_receipt => transport_partial7(a, k, x, before, s, r, bs, prefix, t, other, L.Both{for_kind, data},
          generate((%for_receipt : I.FailureDeliveryReal(a, k, x, _) failed))))

law delivery_partial_reflected_obeys_rule7:
  for -a: I.Environment
  for -k: String
  for -x: I.Scenario
  for +before: List<&2, Q.Frame>
  for +s: D.State
  for +r: S.Response
  for +bs: List<&2, U32>
  for +closure: Bool
  for +prefix: List<&2, U32>
  for +t: Nat
  for +other: List<&2, U32>
  for query_result: {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix})), t) == Some{Q.Interrupted{other}} : Maybe<&2, Q.Frame>}
  for prefix_real: L.Prefix(U32, prefix, bs)
  for failed: I.FailureDeliveryReal(a, k, x, t)
  for without_complete: {Phases.absent(Phases.Complete{}, before) == True{} : Bool}
  for without_interrupted: {Phases.absent(Phases.Interrupted{}, before) == True{} : Bool}
  for prepare: @u: Nat -> @rp: S.Response -> @bytes: List<&2, U32> ->
    {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix})), u) == Some{Q.Prepared{rp, bytes}} : Maybe<&2, Q.Frame>} -> I.Happens(a, k, x, u, I.Prepared{rp, bytes})
  for conclude: @u: Nat -> @rp: S.Response -> @w: D.State -> @closes: Bool ->
    {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix})), u) == Some{Q.Completed{rp, w, closes}} : Maybe<&2, Q.Frame>} -> I.Happens(a, k, x, u, I.Concluded{rp, w, closes})
  for complete: @u: Nat -> @bytes: List<&2, U32> -> I.Happens(a, k, x, u, I.DeliveredEverything{bytes}) ->
    {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix})), u) == Some{Q.Delivered{bytes}} : Maybe<&2, Q.Frame>}
  for interrupted: @u: Nat -> @bytes: List<&2, U32> -> I.Happens(a, k, x, u, I.DeliveryInterrupted{bytes}) ->
    {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix})), u) == Some{Q.Interrupted{bytes}} : Maybe<&2, Q.Frame>}
  K.Rule7(I.DeliveryInterrupted{other}, a, k, x, t)
def delivery_partial_reflected_obeys_rule7(a, k, x, before, s, r, bs, closure, prefix, t, other, query_result, prefix_real, failed,
  without_complete, without_interrupted, prepare, conclude, complete, interrupted):
  F.combined_pair(K.Rule7(I.DeliveryInterrupted{other}, a, k, x, t),
    {Phases.absent(Phases.Interrupted{}, before) == True{} : Bool}, {Phases.absent(Phases.Interrupted{}, before) == True{} : Bool},
    Call.duplicate_equality(Bool, Phases.absent(Phases.Interrupted{}, before), True{}, without_interrupted),
    current => rest => F.combined_pair(K.Rule7(I.DeliveryInterrupted{other}, a, k, x, t),
      {Phases.absent(Phases.Interrupted{}, before) == True{} : Bool}, {Phases.absent(Phases.Interrupted{}, before) == True{} : Bool},
      Call.duplicate_equality(Bool, Phases.absent(Phases.Interrupted{}, before), True{}, rest),
      pos => canonical => summand_real_located(a, k, x, before, s, r, bs, prefix, t, other,
        position_partial_compares(before, s, r, bs, closure, prefix, t, index_delivery(before, s, r, bs), other,
          position_partial_canonical(before, s, r, bs, closure, prefix, pos),
          delivery_partial_located(before, s, r, bs, closure, prefix, t, Q.Interrupted{other}, current, {==}, query_result)), failed,
        real => delivery_partial_canonical_obeys_rule7(a, k, x, before, s, r, bs, closure, prefix, prefix_real, real, without_complete, canonical, prepare, conclude, complete, interrupted))))


def by_index(-T: Type, -P: Nat -> Type, origin: &i: Nat -> P(i), step: @i: Nat -> P(i) -> T) -> T:
  match origin:
    case (i, h): step(i, h)

# Write primitive result: pending is not a write conclusion.
def DeliveryTerminated(delivery: H.Delivery) -> Type:
  match delivery:
    case H.Complete{next}: Unit
    case H.Broken{prefix}: Unit
    case H.PendingDelivery{}: Empty

def closed_after_delivery(+before: List<&2, Q.Frame>, +s: D.State, +r: S.Response, +bs: List<&2, U32>,
  +delivery: H.Delivery, +mark: Q.Frame,
  form: {H.render_delivery(s, bs, True{}, delivery) == [mark, Q.Closed{}] : List<&2, Q.Frame>}) ->
  &i: Nat -> {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, True{}, delivery)), i) == Some{Q.Closed{}} : Maybe<&2, Q.Frame>}:
  (Succ{Q.size(before_of_delivery(before, s, r, bs, True{}))},
    Equal.trans(Maybe<&2, Q.Frame>,
      Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, True{}, delivery)), Succ{Q.size(before_of_delivery(before, s, r, bs, True{}))}),
      Q.query(Q.concatenate(before_of_delivery(before, s, r, bs, True{}), [mark, Q.Closed{}]), Succ{Q.size(before_of_delivery(before, s, r, bs, True{}))}), Some{Q.Closed{}},
      Equal.cong(List<&2, Q.Frame>, Maybe<&2, Q.Frame>, xs => Q.query(xs, Succ{Q.size(before_of_delivery(before, s, r, bs, True{}))}),
        Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, True{}, delivery)),
        Q.concatenate(before_of_delivery(before, s, r, bs, True{}), [mark, Q.Closed{}]),
        Equal.trans(List<&2, Q.Frame>, Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, True{}, delivery)),
          Q.concatenate(before_of_delivery(before, s, r, bs, True{}), H.render_delivery(s, bs, True{}, delivery)),
          Q.concatenate(before_of_delivery(before, s, r, bs, True{}), [mark, Q.Closed{}]), separate_delivery(before, s, r, bs, True{}, delivery),
          Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, ys => Q.concatenate(before_of_delivery(before, s, r, bs, True{}), ys), H.render_delivery(s, bs, True{}, delivery), [mark, Q.Closed{}], form))),
      L.and_right(
        {Q.query(Q.concatenate(before_of_delivery(before, s, r, bs, True{}), [mark, Q.Closed{}]), Q.size(before_of_delivery(before, s, r, bs, True{}))) == Some{mark} : Maybe<&2, Q.Frame>},
        {Q.query(Q.concatenate(before_of_delivery(before, s, r, bs, True{}), [mark, Q.Closed{}]), Succ{Q.size(before_of_delivery(before, s, r, bs, True{}))}) == Some{Q.Closed{}} : Maybe<&2, Q.Frame>},
        Q.two_frames_after_prefix(before_of_delivery(before, s, r, bs, True{}), Nil{}, mark, Q.Closed{}))))

def delivery_terminated_closes(+before: List<&2, Q.Frame>, +s: D.State, +r: S.Response, +bs: List<&2, U32>,
  delivery: H.Delivery, terminated: DeliveryTerminated(delivery)) ->
  &i: Nat -> {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, True{}, delivery)), i) == Some{Q.Closed{}} : Maybe<&2, Q.Frame>}:
  match delivery:
    case H.Complete{+next}: closed_after_delivery(before, s, r, bs, H.Complete{next}, Q.Delivered{bs}, {==})
    case H.Broken{+prefix}: closed_after_delivery(before, s, r, bs, H.Broken{prefix}, Q.Interrupted{prefix}, {==})
    case H.PendingDelivery{}: match terminated:

def close_of_write(-a: I.Environment, -k: String, -x: I.Scenario, +before: List<&2, Q.Frame>,
  +s: D.State, +r: S.Response, +bs: List<&2, U32>, closure: Bool, +delivery: H.Delivery,
  available: I.Processable(a, x) -> DeliveryTerminated(delivery),
  close: @u: Nat -> {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, delivery)), u) == Some{Q.Closed{}} : Maybe<&2, Q.Frame>} -> I.Happens(a, k, x, u, I.ClosedChannel{})) ->
  K.CloseEventually(closure, a, k, x):
  match closure:
    case False{}: Unit{}
    case True{}: can => by_index(I.InSomeMoment(a, k, x, I.ClosedChannel{}),
      u => {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, True{}, delivery)), u) == Some{Q.Closed{}} : Maybe<&2, Q.Frame>},
      delivery_terminated_closes(before, s, r, bs, delivery, available(can)), +u => query_result => (u, close(u, query_result)))

# Uniqueness of Concluded, now using actual closure policy instead of fixed False.
def conclusion_located_in_closure(+before: List<&2, Q.Frame>, +s: D.State, +r: S.Response, +bs: List<&2, U32>,
  +closure: Bool, +delivery: H.Delivery, +t: Nat, +q: Q.Frame,
  without: {Phases.absent(Phases.Conclusion{}, before) == True{} : Bool},
  target: {Phases.of_that_kind(Phases.Conclusion{}, q) == True{} : Bool},
  query_result: {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, delivery)), t) == Some{q} : Maybe<&2, Q.Frame>}) ->
  L.E<{t == Nat.add(Q.size(before), local_conclusion(s, r, bs)) : Nat}, {q == Q.Completed{r, s, closure} : Q.Frame}>:
  F.combined_pair(L.E<{t == Nat.add(Q.size(before), local_conclusion(s, r, bs)) : Nat}, {q == Q.Completed{r, s, closure} : Q.Frame}>,
    {Phases.of_that_kind(Phases.Conclusion{}, q) == True{} : Bool}, {Phases.of_that_kind(Phases.Conclusion{}, q) == True{} : Bool},
    Call.duplicate_equality(Bool, Phases.of_that_kind(Phases.Conclusion{}, q), True{}, target),
    for_prefix => for_end => by_index(
      L.E<{t == Nat.add(Q.size(before), local_conclusion(s, r, bs)) : Nat}, {q == Q.Completed{r, s, closure} : Q.Frame}>,
      u => L.E<{t == Nat.add(Q.size(before), u) : Nat}, {Q.query(H.render_conclusion(N.Conclusion{s, r, bs}, closure, delivery), u) == Some{q} : Maybe<&2, Q.Frame>}>,
      Phases.locate_in_suffix(Phases.Conclusion{}, before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, delivery), t, q, without, for_prefix, query_result),
      +u => part => F.combined_pair(
        L.E<{t == Nat.add(Q.size(before), local_conclusion(s, r, bs)) : Nat}, {q == Q.Completed{r, s, closure} : Q.Frame}>,
        {t == Nat.add(Q.size(before), u) : Nat}, {Q.query(H.render_conclusion(N.Conclusion{s, r, bs}, closure, delivery), u) == Some{q} : Maybe<&2, Q.Frame>}, part,
        pos => obtained => F.combined_pair(
          L.E<{t == Nat.add(Q.size(before), local_conclusion(s, r, bs)) : Nat}, {q == Q.Completed{r, s, closure} : Q.Frame}>,
          {u == local_conclusion(s, r, bs) : Nat}, {q == Q.Completed{r, s, closure} : Q.Frame}, Phases.conclusion_in_end_and_unique(s, r, bs, closure, delivery, u, q, for_end, obtained),
          index => equal => L.Both{Equal.trans(Nat, t, Nat.add(Q.size(before), u), Nat.add(Q.size(before), local_conclusion(s, r, bs)), pos,
            Equal.cong(Nat, Nat, j => Nat.add(Q.size(before), j), u, local_conclusion(s, r, bs), index)), equal}))))

def fields_conclusion_in_closure(+r: S.Response, +s: D.State, +closes: Bool, +r0: S.Response, +s0: D.State, +closure: Bool,
  equal: {Q.Completed{r, s, closes} == Q.Completed{r0, s0, closure} : Q.Frame}) ->
  L.E<{r == r0 : S.Response}, {s == s0 : D.State}>:
  F.combined_pair(L.E<{r == r0 : S.Response}, {s == s0 : D.State}>,
    {Q.Completed{r, s, closes} == Q.Completed{r0, s0, closure} : Q.Frame}, {Q.Completed{r, s, closes} == Q.Completed{r0, s0, closure} : Q.Frame},
    Call.duplicate_equality(Q.Frame, Q.Completed{r, s, closes}, Q.Completed{r0, s0, closure}, equal),
    response => state => L.Both{
      F.some_injective(S.Response, r, r0, Equal.cong(Q.Frame, Maybe<&2, S.Response>, response_completed, Q.Completed{r, s, closes}, Q.Completed{r0, s0, closure}, response)),
      F.some_injective(D.State, s, s0, Equal.cong(Q.Frame, Maybe<&2, D.State>, state_completed, Q.Completed{r, s, closes}, Q.Completed{r0, s0, closure}, state))})

def conclusion_compares_in_closure(+before: List<&2, Q.Frame>, +s: D.State, +r: S.Response, +bs: List<&2, U32>, +closure: Bool,
  -u: Nat, +r2: S.Response, +s2: D.State, +f2: Bool,
  local: L.E<{u == Nat.add(Q.size(before), local_conclusion(s, r, bs)) : Nat}, {Q.Completed{r2, s2, f2} == Q.Completed{r, s, closure} : Q.Frame}>) ->
  L.E<{u == Nat.add(Q.size(before), local_conclusion(s, r, bs)) : Nat}, L.E<{r2 == r : S.Response}, {s2 == s : D.State}>>:
  match local:
    case L.Both{pos, fields}: L.Both{pos, fields_conclusion_in_closure(r2, s2, f2, r, s, closure, fields)}

law conclusion_in_closure_obeys_rule7:
  for -a: I.Environment
  for -k: String
  for -x: I.Scenario
  for +before: List<&2, Q.Frame>
  for +s: D.State
  for +r: S.Response
  for +bs: List<&2, U32>
  for +closure: Bool
  for +delivery: H.Delivery
  for without_conclude: {Phases.absent(Phases.Conclusion{}, before) == True{} : Bool}
  for allowed: K.ClosingAllowed(a, k, x, Nat.add(Q.size(before), local_conclusion(s, r, bs)), closure)
  for available: I.Processable(a, x) -> DeliveryTerminated(delivery)
  for prepare: @u: Nat -> @rp: S.Response -> @bytes: List<&2, U32> ->
    {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, delivery)), u) == Some{Q.Prepared{rp, bytes}} : Maybe<&2, Q.Frame>} -> I.Happens(a, k, x, u, I.Prepared{rp, bytes})
  for conclude: @u: Nat -> @rp: S.Response -> @w: D.State -> @closes: Bool -> I.Happens(a, k, x, u, I.Concluded{rp, w, closes}) ->
    {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, delivery)), u) == Some{Q.Completed{rp, w, closes}} : Maybe<&2, Q.Frame>}
  for close: @u: Nat -> {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, delivery)), u) == Some{Q.Closed{}} : Maybe<&2, Q.Frame>} -> I.Happens(a, k, x, u, I.ClosedChannel{})
  K.Rule7(I.Concluded{r, s, closure}, a, k, x, Nat.add(Q.size(before), local_conclusion(s, r, bs)))
def conclusion_in_closure_obeys_rule7(a, k, x, before, s, r, bs, closure, delivery, without_conclude, allowed, available, prepare, conclude, close):
  L.Both{(bs, Nat.add(Q.size(before), 0n), L.Both{Q.order_shifted(Q.size(before), 0n, local_conclusion(s, r, bs), {==}),
      prepare(Nat.add(Q.size(before), 0n), r, bs, Q.query_after_prefix(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, delivery), 0n))}),
    L.Both{L.Both{allowed, close_of_write(a, k, x, before, s, r, bs, closure, delivery, available, close)},
      +u => +r2 => +s2 => +f2 => fact => conclusion_compares_in_closure(before, s, r, bs, closure, u, r2, s2, f2,
        conclusion_located_in_closure(before, s, r, bs, closure, delivery, u, Q.Completed{r2, s2, f2}, without_conclude, {==}, conclude(u, r2, s2, f2, fact)))}}

def transport_conclusion7_in_closure(-a: I.Environment, -k: String, -x: I.Scenario, +before: List<&2, Q.Frame>,
  +s: D.State, +r: S.Response, +bs: List<&2, U32>, +closure: Bool, -t: Nat, +q: Q.Frame,
  local: L.E<{t == Nat.add(Q.size(before), local_conclusion(s, r, bs)) : Nat}, {q == Q.Completed{r, s, closure} : Q.Frame}>,
  canonical: K.Rule7(I.Concluded{r, s, closure}, a, k, x, Nat.add(Q.size(before), local_conclusion(s, r, bs)))) ->
  K.Rule7(fact_of_conclusion(q), a, k, x, t):
  match local:
    case L.Both{pos, frame}:
      %Equal.sym(Nat, t, Nat.add(Q.size(before), local_conclusion(s, r, bs)), pos) : K.Rule7(fact_of_conclusion(q), a, k, x, _)
      %Equal.sym(Q.Frame, q, Q.Completed{r, s, closure}, frame) : K.Rule7(fact_of_conclusion(_), a, k, x, Nat.add(Q.size(before), local_conclusion(s, r, bs)))
      canonical


# Header policy: a recoverable packet error occurs only after receiving the body.
def FramingReached(pre: H.Preprocessing, -disposition: X.Disposition) -> Type:
  match pre:
    case H.FailureFraming{id, fatal}:
      match fatal:
        case False{}: &br: List<&2, U32> -> {disposition == X.ProcessBody{br} : X.Disposition}
        case True{}: Unit
    case _: Unit

def input_closes(branch: H.Branch) -> Bool:
  match branch:
    case H.InputRefusal{e, closes, delivery}: closes
    case _: False{}

def is_input(branch: H.Branch) -> Bool:
  match branch:
    case H.InputRefusal{error, closes, en}: True{}
    case _: False{}

def cleanup_negative_and_input(r: P.Request, ctx: D.Context, xs: List<&2, Q.FrameExec>, p: N.Prepared,
  li: H.Cleanup, en: H.Delivery) -> {is_input(H.decide_cleanup(r, ctx, xs, p, li, en)) == False{} : Bool}:
  match li:
    case H.Clears{}: {==}
    case H.ErrorCleanup{id, fatal}: {==}
    case H.FatalAfterStore{stage, id}: {==}
    case H.PendingCleanup{}: {==}

def execution_negative_and_input(r: P.Request, ctx: D.Context, ex: H.OutputExecution, li: H.Cleanup, en: H.Delivery) ->
  {is_input(H.decide_execution(r, ctx, ex, li, en)) == False{} : Bool}:
  match ex:
    case H.Finalized{xs, p}: cleanup_negative_and_input(r, ctx, xs, p, li, en)
    case H.ErrorExecution{point, stage, id, fatal}: {==}
    case H.PendingExecution{point}: {==}

def judgment_negative_and_input(r: P.Request, ctx: D.Context, data: H.DataTools) ->
  {is_input(H.decide_judgment(r, ctx, data)) == False{} : Bool}:
  match data:
    case H.DataTools{j, ex, li, en, pre}:
      match j:
        case H.Accepted{}: execution_negative_and_input(r, ctx, ex, li, en)
        case H.Refused{}: {==}
        case H.ErrorJudgment{id, fatal}: {==}
        case H.PendingJudgment{}: {==}

def identity_negative_and_input(ctx: Maybe<&2, D.Context>, r: P.Request, data: H.DataTools) ->
  {is_input(H.decide_identity(ctx, r, data)) == False{} : Bool}:
  match ctx:
    case None{}:
      match data:
        case H.DataTools{j, ex, li, en, pre}: {==}
    case Some{c}: judgment_negative_and_input(r, c, data)

def authentication_negative_and_input(pre: H.Preprocessing, s: D.State, +r: P.Request, data: H.DataTools) ->
  {is_input(H.decide_authentication(pre, s, r, data)) == False{} : Bool}:
  match pre:
    case H.FailureAuth{id, fatal}: {==}
    case H.PendingAuth{}: {==}
    case H.Normal{}: identity_negative_and_input(D.authenticate(s, I.credential(r)), r, data)
    case H.FailureDecode{id, fatal}: identity_negative_and_input(D.authenticate(s, I.credential(r)), r, data)
    case H.FailureFraming{id, fatal}: identity_negative_and_input(D.authenticate(s, I.credential(r)), r, data)
    case H.PendingDecode{}: identity_negative_and_input(D.authenticate(s, I.credential(r)), r, data)
    case H.PendingFraming{}: identity_negative_and_input(D.authenticate(s, I.credential(r)), r, data)

def without_input_negative_closes(branch: H.Branch, negative: {is_input(branch) == False{} : Bool}) -> {input_closes(branch) == False{} : Bool}:
  match branch:
    case H.InputRefusal{e, +closes, en}: F.absurd_boolean({closes == False{} : Bool}, Equal.sym(Bool, True{}, False{}, negative))
    case H.AutRefusal{r, en}: {==}
    case H.GateRefusal{r, ctx, en}: {==}
    case H.Executed{r, ctx, qs, p, en}: {==}
    case H.FailureBefore{phase, stage, id, fatal, en}: {==}
    case H.InitialOk{}: {==}
    case H.InitialRefusal{status}: {==}
    case H.InitialFailure{accepts, stage, id, fatal}: {==}
    case H.WithoutResponse{}: {==}
    case H.FatalAfterPublication{r, ctx, qs, p, stage, id}: {==}
    case H.Pending{phase}: {==}
    case H.InitialPending{accepts}: {==}

def pre_negative_closes(pre: Input.PreAuthentication, +data: H.DataTools) ->
  {input_closes(H.decide_pre(pre, data)) == False{} : Bool}:
  match pre:
    case Input.InputReady{+s, +r}: without_input_negative_closes(H.decide_authentication(H.preprocessing(data), s, r, data), authentication_negative_and_input(H.preprocessing(data), s, r, data))
    case Input.ErrorMessage{status}:
      match data:
        case H.DataTools{j, ex, li, en, pre}: {==}
    case Input.ErrorTransport{}:
      match data:
        case H.DataTools{j, ex, li, en, pre}: {==}

def decode_negative_closes(pre: H.Preprocessing, bs: List<&2, U32>, e: D.Schema, lim: S.Limits, data: H.DataTools) ->
  {input_closes(H.decide_decode(pre, bs, e, lim, data)) == False{} : Bool}:
  match pre:
    case H.FailureDecode{id, fatal}: {==}
    case H.PendingDecode{}: {==}
    case H.Normal{}: pre_negative_closes(Input.decode(bs, e, lim), data)
    case H.FailureAuth{id, fatal}: pre_negative_closes(Input.decode(bs, e, lim), data)
    case H.FailureFraming{id, fatal}: pre_negative_closes(Input.decode(bs, e, lim), data)
    case H.PendingAuth{}: pre_negative_closes(Input.decode(bs, e, lim), data)
    case H.PendingFraming{}: pre_negative_closes(Input.decode(bs, e, lim), data)

def packet_negative_closes(packet: Maybe<&2, List<&2, U32>>, e: D.Schema, lim: S.Limits, +data: H.DataTools) ->
  {input_closes(H.decide_packet(packet, e, lim, data)) == False{} : Bool}:
  match packet:
    case None{}:
      match data:
        case H.DataTools{j, ex, li, en, pre}: {==}
    case Some{bs}: decode_negative_closes(H.preprocessing(data), bs, e, lim, data)

# This type concerns only the computed framing bit, not Law7.
def PolicyClosure(disposition: X.Disposition, branch: H.Branch) -> Type:
  match branch:
    case H.InputRefusal{e, closes, en}: I.ClosingDisposition(disposition, closes)
    case H.AutRefusal{r, en}: I.ClosingDisposition(disposition, False{})
    case H.GateRefusal{r, ctx, en}: I.ClosingDisposition(disposition, False{})
    case H.Executed{r, ctx, qs, p, en}: I.ClosingDisposition(disposition, False{})
    case H.FailureBefore{phase, stage, id, fatal, en}:
      match fatal:
        case False{}: I.ClosingDisposition(disposition, False{})
        case True{}: Unit
    case _: Unit

def body_has_policy(+br: List<&2, U32>, branch: H.Branch,
  negative_closes: {input_closes(branch) == False{} : Bool}) -> PolicyClosure(X.ProcessBody{br}, branch):
  match branch:
    case H.InputRefusal{e, closes, en}: negative_closes
    case H.AutRefusal{r, en}: {==}
    case H.GateRefusal{r, ctx, en}: {==}
    case H.Executed{r, ctx, qs, p, en}: {==}
    case H.FailureBefore{phase, stage, id, fatal, en}:
      match fatal:
        case False{}: {==}
        case True{}: Unit{}
    case H.InitialOk{}: Unit{}
    case H.InitialRefusal{status}: Unit{}
    case H.InitialFailure{accepts, stage, id, fatal}: Unit{}
    case H.WithoutResponse{}: Unit{}
    case H.FatalAfterPublication{r, ctx, qs, p, stage, id}: Unit{}
    case H.Pending{phase}: Unit{}
    case H.InitialPending{accepts}: Unit{}

def disposition_has_policy(+d: X.Disposition, +be: List<&2, U32>, +e: D.Schema, +lim: S.Limits,
  +data: H.DataTools) -> PolicyClosure(d, H.decide_disposition(d, be, e, lim, data)):
  match d:
    case X.CloseWithoutResponse{}: Unit{}
    case X.RefuseClose{s}:
      match data:
        case H.DataTools{j, ex, li, en, pre}: {==}
    case X.RefuseContinue{s}:
      match data:
        case H.DataTools{j, ex, li, en, pre}: {==}
    case X.ProcessBody{+br}: body_has_policy(br, H.decide_packet(Transport.join(be, br), e, lim, data), packet_negative_closes(Transport.join(be, br), e, lim, data))

def framing_has_policy(pre: H.Preprocessing, +d: X.Disposition, +be: List<&2, U32>, +e: D.Schema, +lim: S.Limits, +data: H.DataTools,
  reached: FramingReached(pre, d)) -> PolicyClosure(d, H.decide_framing(pre, d, be, e, lim, data)):
  match pre:
    case H.FailureFraming{id, fatal}:
      match fatal:
        case True{}: Unit{}
        case False{}:
          match reached:
            case (br, equal):
              %Equal.sym(X.Disposition, d, X.ProcessBody{br}, equal) : I.ClosingDisposition(_, False{})
              {==}
    case H.PendingFraming{}: Unit{}
    case H.Normal{}: disposition_has_policy(d, be, e, lim, data)
    case H.FailureDecode{id, fatal}: disposition_has_policy(d, be, e, lim, data)
    case H.FailureAuth{id, fatal}: disposition_has_policy(d, be, e, lim, data)
    case H.PendingDecode{}: disposition_has_policy(d, be, e, lim, data)
    case H.PendingAuth{}: disposition_has_policy(d, be, e, lim, data)

law decision_has_policy_of_closure:
  for ~c: S.Configuration
  for +rx: X.Reception
  for +be: List<&2, U32>
  for +data: H.DataTools
  for reached: FramingReached(H.preprocessing(data), X.decide_reception(c, rx))
  PolicyClosure(X.decide_reception(c, rx), H.decide(c, rx, be, data))
def decision_has_policy_of_closure(c, rx, be, data, reached):
  %Equal.sym(H.Branch, H.decide(c, rx, be, data), H.decide_framing(H.preprocessing(data), X.decide_reception(c, rx), be, S.schema(c), S.limits(c), data),
    Two.decide_by_reception(c, rx, be, data)) : PolicyClosure(X.decide_reception(c, rx), _)
  framing_has_policy(H.preprocessing(data), X.decide_reception(c, rx), be, S.schema(c), S.limits(c), data, reached)

def PolicyOfClosure(d: X.Disposition, q: Maybe<&2, Closures.Closure>) -> Type:
  match q:
    case None{}: Unit
    case Some{Closures.Closure{before, c, closes, delivery, origin}}: I.ClosingDisposition(d, closes)

# Availability of write/flush on the selected technical result.
# Receives no conclusion, publication or closure fact here.
def WritesAvailable(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception,
  q: Maybe<&2, Closures.Closure>) -> Type:
  match q:
    case None{}: Unit
    case Some{Closures.Closure{before, completed, closes, delivery, origin}}:
      I.Processable(Source.environment(source), I.Serve{world, c, s, rx}) -> DeliveryTerminated(delivery)

def policy_of_error(q: Maybe<&2, List<&2, U32>>, +d: X.Disposition, before: List<&2, Q.Frame>, s: D.State,
  e: Errors.Error, +closes: Bool, delivery: H.Delivery, origin: H.Branch, policy: I.ClosingDisposition(d, closes)) ->
  PolicyOfClosure(d, Closures.error(q, before, s, e, closes, delivery, origin)):
  match q:
    case None{}: Unit{}
    case Some{bs}: policy

def policy_of_error_fixed(+d: X.Disposition, before: List<&2, Q.Frame>, s: D.State,
  +e: Errors.Error, +closes: Bool, delivery: H.Delivery, origin: H.Branch, policy: I.ClosingDisposition(d, closes)) ->
  PolicyOfClosure(d, Closures.close_error(before, s, e, closes, delivery, origin)):
  policy_of_error(P.frame(S.response_value(S.response_error(Errors.status(e)))), d, before, s, e, closes, delivery, origin, policy)

def policy_of_branch(+d: X.Disposition, +m: H.Micro, +s: D.State, branch: H.Branch,
  policy: PolicyClosure(d, branch)) -> PolicyOfClosure(d, Closures.of_branch(m, s, branch)):
  match branch:
    case H.InputRefusal{+e, +closes, +en}: policy_of_error_fixed(d, H.micro_input(m), s, Closures.error_of_input(e), closes, en, H.InputRefusal{e, closes, en}, policy)
    case H.AutRefusal{+r, +en}: policy_of_error_fixed(d, Closures.before_authentication(m, r), s, Errors.Authentication{}, False{}, en, H.AutRefusal{r, en}, policy)
    case H.GateRefusal{+r, +ctx, +en}: policy_of_error_fixed(d, Closures.before_gate(m, r, ctx), s, Errors.Certificate{}, False{}, en, H.GateRefusal{r, ctx, en}, policy)
    case H.Executed{r, ctx, qs, p, en}: policy
    case H.FailureBefore{+phase, +stage, +id, fatal, +en}:
      match fatal:
        case True{}: Unit{}
        case False{}: policy_of_error_fixed(d, Closures.before_failure(m, phase, stage, id, False{}), s, Errors.Failure{}, False{}, en, H.FailureBefore{phase, stage, id, False{}, en}, policy)
    case H.InitialOk{}: Unit{}
    case H.InitialRefusal{status}: Unit{}
    case H.InitialFailure{accepts, stage, id, fatal}: Unit{}
    case H.WithoutResponse{}: Unit{}
    case H.FatalAfterPublication{r, ctx, qs, p, stage, id}: Unit{}
    case H.Pending{phase}: Unit{}
    case H.InitialPending{accepts}: Unit{}

def configure_policy(+d: X.Disposition, q: Maybe<&2, Closures.Closure>, policy: PolicyOfClosure(d, q)) ->
  PolicyOfClosure(d, Closures.configure(q)):
  match q:
    case None{}: Unit{}
    case Some{Closures.Closure{before, c, closes, delivery, origin}}: policy

def policy_of_route(+d: X.Disposition, +m: H.Micro, +s: D.State, +branch: H.Branch, policy: PolicyClosure(d, branch)) ->
  PolicyOfClosure(d, Closures.closure_of_branch(m, s, branch)):
  configure_policy(d, Closures.of_branch(m, s, branch), policy_of_branch(d, m, s, branch, policy))


def ReachedPacket(~c: S.Configuration, +rx: X.Reception, data: Source.CallData) -> Type:
  match data:
    case Source.CallData{cf, pf, cert, terminates, be, tools, micro}:
      FramingReached(H.preprocessing(tools), X.decide_reception(c, rx))

def policy_of_data(~c: S.Configuration, +rx: X.Reception, data: Source.CallData,
  reached: ReachedPacket(c, rx, data)) -> PolicyClosure(X.decide_reception(c, rx), Lig.branch_of_data(c, rx, data)):
  match data:
    case Source.CallData{cf, pf, cert, terminates, be, tools, micro}:
      decision_has_policy_of_closure(c, rx, be, tools, reached)

def conclusion_source_in_closure(~source: Source.Source, ~c: S.Configuration, +world: Nat, +initial: D.State,
  +rx: X.Reception, +before: List<&2, Q.Frame>, +s: D.State, +r: S.Response, +bs: List<&2, U32>, +closure: Bool, +delivery: H.Delivery,
  +t: Nat, +r2: S.Response, +s2: D.State, +f2: Bool,
  canonical: {I.Serve{world, c, initial, rx} == Source.scenario(source, world) : I.Scenario},
  +same: {Vis.frames_call(c, initial, rx, Source.call(source, world)) == Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, delivery)) : List<&2, Q.Frame>},
  +without_conclude: {Phases.absent(Phases.Conclusion{}, before) == True{} : Bool},
  policy: I.ClosingDisposition(X.decide_reception(c, rx), closure),
  available: I.Processable(Source.environment(source), I.Serve{world, c, initial, rx}) -> DeliveryTerminated(delivery),
  query_result: {Q.query(Vis.frames_call(c, initial, rx, Source.call(source, world)), t) == Some{Q.Completed{r2, s2, f2}} : Maybe<&2, Q.Frame>}) ->
  K.Rule7(I.Concluded{r2, s2, f2}, Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, rx}, t):
  F.combined_pair(K.Rule7(I.Concluded{r2, s2, f2}, Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, rx}, t),
    {I.Serve{world, c, initial, rx} == Source.scenario(source, world) : I.Scenario},
    {I.Serve{world, c, initial, rx} == Source.scenario(source, world) : I.Scenario},
    Call.duplicate_equality(I.Scenario, I.Serve{world, c, initial, rx}, Source.scenario(source, world), canonical),
    for_preparation => for_closure => transport_conclusion7_in_closure(Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, rx}, before, s, r, bs, closure, t, Q.Completed{r2, s2, f2},
      conclusion_located_in_closure(before, s, r, bs, closure, delivery, t, Q.Completed{r2, s2, f2}, without_conclude, {==},
        (%same : {Q.query(_, t) == Some{Q.Completed{r2, s2, f2}} : Maybe<&2, Q.Frame>} query_result)),
      conclusion_in_closure_obeys_rule7(Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, rx}, before, s, r, bs, closure, delivery,
        without_conclude, L.Left{policy}, available,
        +u => +rp => +bytes => obtained => Lig.introduce_in_list(source, c, world, initial, rx,
          Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, delivery)), u, Q.Prepared{rp, bytes}, I.Prepared{rp, bytes}, for_preparation, same, obtained, {==}, Unit{}),
        +u => +rp => +w => +closes => fact => Lig.extract_in_list(source, c, world, initial, rx,
          Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, delivery)), u, I.Concluded{rp, w, closes}, same, Unit{}, fact),
        +u => obtained => Lig.introduce_in_list(source, c, world, initial, rx,
          Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, delivery)), u, Q.Closed{}, I.ClosedChannel{}, for_closure, same, obtained, {==}, Unit{}))))

def consume_conclusion_selected(~source: Source.Source, ~c: S.Configuration, +world: Nat, +initial: D.State,
  +rx: X.Reception, +branch: H.Branch, q: Maybe<&2, Closures.Closure>, +t: Nat, +r: S.Response, +s: D.State, +closes: Bool,
  canonical: {I.Serve{world, c, initial, rx} == Source.scenario(source, world) : I.Scenario},
  form: Closures.Form(Vis.frames_call(c, initial, rx, Source.call(source, world)), branch, q),
  policy: PolicyOfClosure(X.decide_reception(c, rx), q), available: WritesAvailable(source, c, world, initial, rx, q),
  query_result: {Q.query(Vis.frames_call(c, initial, rx, Source.call(source, world)), t) == Some{Q.Completed{r, s, closes}} : Maybe<&2, Q.Frame>}) ->
  K.Rule7(I.Concluded{r, s, closes}, Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, rx}, t):
  match q:
    case None{}: L.ex_false(K.Rule7(I.Concluded{r, s, closes}, Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, rx}, t),
      Phases.absent_excludes_query(Phases.Conclusion{}, Vis.frames_call(c, initial, rx, Source.call(source, world)), t, Q.Completed{r, s, closes}, form, {==}, query_result))
    case Some{Closures.Closure{before, N.Conclusion{w, rp, bs}, closure, delivery, origin}}:
      match form:
        case L.Both{same_branch, L.Both{trace, L.Both{pub, concl}}}:
          conclusion_source_in_closure(source, c, world, initial, rx, before, w, rp, bs, closure, delivery, t, r, s, closes,
            canonical, trace, concl, policy, available, query_result)

def conclusion_of_call_obeys_rule7(~source: Source.Source, ~c: S.Configuration, +world: Nat, +initial: D.State,
  +rx: X.Reception, +t: Nat, +r: S.Response, +s: D.State, +closes: Bool,
  reached: ReachedPacket(c, rx, Source.call(source, world)),
  available: WritesAvailable(source, c, world, initial, rx,
    Closures.closure_of_branch(Lig.micro_of_data(Source.call(source, world)), initial, Lig.branch_of_data(c, rx, Source.call(source, world)))),
  observed: I.Happens(Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, rx}, t, I.Concluded{r, s, closes})) ->
  K.Rule7(I.Concluded{r, s, closes}, Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, rx}, t):
  F.combined_pair(K.Rule7(I.Concluded{r, s, closes}, Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, rx}, t),
    {Source.artifact(source) == Source.artifact(source) : String},
    L.E<{I.Serve{world, c, initial, rx} == Source.scenario(source, world) : I.Scenario}, Source.of_route(source, I.Serve{world, c, initial, rx}, t, I.Concluded{r, s, closes})>,
    Source.eliminate_fact_literal(source, Source.artifact(source), I.Serve{world, c, initial, rx}, t, I.Concluded{r, s, closes}, observed),
    name => origin => F.combined_pair(K.Rule7(I.Concluded{r, s, closes}, Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, rx}, t),
      {I.Serve{world, c, initial, rx} == Source.scenario(source, world) : I.Scenario}, Source.of_route(source, I.Serve{world, c, initial, rx}, t, I.Concluded{r, s, closes}), origin,
      canonical => obs => consume_conclusion_selected(source, c, world, initial, rx, Lig.branch_of_data(c, rx, Source.call(source, world)),
        Closures.closure_of_branch(Lig.micro_of_data(Source.call(source, world)), initial, Lig.branch_of_data(c, rx, Source.call(source, world))), t, r, s, closes, canonical,
        (%Equal.sym(List<&2, Q.Frame>, Vis.frames_call(c, initial, rx, Source.call(source, world)),
          H.render(Lig.micro_of_data(Source.call(source, world)), initial, Lig.branch_of_data(c, rx, Source.call(source, world))),
          Lig.frames_follow_o_branch(c, initial, rx, Source.call(source, world))) : Closures.Form(_, Lig.branch_of_data(c, rx, Source.call(source, world)),
            Closures.closure_of_branch(Lig.micro_of_data(Source.call(source, world)), initial, Lig.branch_of_data(c, rx, Source.call(source, world))))
          Closures.form_of_route(Lig.micro_of_data(Source.call(source, world)), initial, Lig.branch_of_data(c, rx, Source.call(source, world)))),
        policy_of_route(X.decide_reception(c, rx), Lig.micro_of_data(Source.call(source, world)), initial, Lig.branch_of_data(c, rx, Source.call(source, world)),
          policy_of_data(c, rx, Source.call(source, world), reached)), available,
        Lig.frame_of_observation(source, c, initial, rx, Source.call(source, world), t, I.Concluded{r, s, closes}, Unit{}, obs))))


# Fixed-error data computed by the same encoder; the cause is proved separately.
def data_of_error_prepared(~c: S.Configuration, +status: S.Status, +bs: List<&2, U32>,
  configuration: {R.configuration_is_valid(c) == True{} : Bool}, error: Preparation.Error(status),
  message: P.Message(S.response_value(S.response_error(status)), bs)) ->
  L.E<I.ErrorFixed(S.response_error(status)), L.E<P.Message(S.response_value(S.response_error(status)), bs),
    {R.fits(R.limit_response(S.limits(c)), S.response_value(S.response_error(status))) == True{} : Bool}>>:
  F.combined_pair(
    L.E<I.ErrorFixed(S.response_error(status)), L.E<P.Message(S.response_value(S.response_error(status)), bs),
      {R.fits(R.limit_response(S.limits(c)), S.response_value(S.response_error(status))) == True{} : Bool}>>,
    I.ErrorFixed(S.response_error(status)), {R.fits(R.limit_response(S.limits(c)), S.response_value(S.response_error(status))) == True{} : Bool},
    Preparation.error_preparable(status, S.limits(c), Preparation.limits_of_configuration(c, configuration), error),
    payload => size => L.Both{payload, L.Both{message, size}})

law preparation_fixed_combined_cause_real_obeys_rule7:
  for ~c: S.Configuration
  for -a: I.Environment
  for -k: String
  for -x: I.Scenario
  for -t: Nat
  for +status: S.Status
  for +bs: List<&2, U32>
  for configuration: {I.configuration(x) == c : S.Configuration}
  for is_valid: {R.configuration_is_valid(c) == True{} : Bool}
  for error: Preparation.Error(status)
  for message: P.Message(S.response_value(S.response_error(status)), bs)
  for cause: I.ResponseJustified(S.response_error(status), a, k, x, t)
  K.Rule7(I.Prepared{S.response_error(status), bs}, a, k, x, t)
def preparation_fixed_combined_cause_real_obeys_rule7(c, a, k, x, t, status, bs, configuration, is_valid, error, message, cause):
  F.combined_pair(K.Rule7(I.Prepared{S.response_error(status), bs}, a, k, x, t),
    I.ErrorFixed(S.response_error(status)), L.E<P.Message(S.response_value(S.response_error(status)), bs),
      {R.fits(R.limit_response(S.limits(I.configuration(x))), S.response_value(S.response_error(status))) == True{} : Bool}>,
    (%Equal.sym(S.Configuration, I.configuration(x), c, configuration) :
      L.E<I.ErrorFixed(S.response_error(status)), L.E<P.Message(S.response_value(S.response_error(status)), bs),
        {R.fits(R.limit_response(S.limits(_)), S.response_value(S.response_error(status))) == True{} : Bool}>>
      data_of_error_prepared(c, status, bs, is_valid, error, message)),
    payload => rest => F.combined_pair(K.Rule7(I.Prepared{S.response_error(status), bs}, a, k, x, t),
      P.Message(S.response_value(S.response_error(status)), bs),
      {R.fits(R.limit_response(S.limits(I.configuration(x))), S.response_value(S.response_error(status))) == True{} : Bool}, rest,
      encoded => size => L.Both{payload, L.Both{encoded, L.Both{size, cause}}}))


# The prepare equation determines ALL fields, not just status.
law normalize_prepared_real:
  for ~c: S.Configuration
  for +w: D.State
  for +ts: List<&2, S.OperationEvent>
  for +proposal: S.Response
  for +p: N.Prepared
  for obtained: {N.prepare(N.Stopped{w, ts, proposal}, c) == Some{p} : Maybe<&2, N.Prepared>}
  L.E<{p == N.Prepared{w, ts, R.finalize(proposal, c, w), Preparation.bytes_prepared(p)} : N.Prepared},
    P.Message(S.response_value(R.finalize(proposal, c, w)), Preparation.bytes_prepared(p))>
def normalize_prepared_real(c, w, ts, proposal, p, obtained):
  match p:
    case N.Prepared{pw, pts, pr, bs}:
      Preparation.prepare_preserves_response_state_events_and_bytes(N.Stopped{w, ts, proposal}, c, N.Prepared{pw, pts, pr, bs}, obtained)


# The write receipt refers to the complete bytes of that actual proposal.
def PrefixOfWrite(c: N.Conclusion, en: H.Delivery) -> Type:
  match c:
    case N.Conclusion{s, r, bs}:
      match en:
        case H.Broken{prefix}: L.Prefix(U32, prefix, bs)
        case _: Unit

def PrefixesOfClosure(q: Maybe<&2, Closures.Closure>) -> Type:
  match q:
    case None{}: Unit
    case Some{Closures.Closure{before, c, closes, en, origin}}: PrefixOfWrite(c, en)

type FactDelivery is Data:
  CompleteObserved{bytes: List<&2, U32>}
  PartialObserved{bytes: List<&2, U32>}

def fact_delivery(e: FactDelivery) -> I.Fact:
  match e:
    case CompleteObserved{bs}: I.DeliveredEverything{bs}
    case PartialObserved{bs}: I.DeliveryInterrupted{bs}

def frame_delivery(e: FactDelivery) -> Q.Frame:
  match e:
    case CompleteObserved{bs}: Q.Delivered{bs}
    case PartialObserved{bs}: Q.Interrupted{bs}

def delivery_without_closure_impossible(-a: I.Environment, -k: String, -x: I.Scenario, +xs: List<&2, Q.Frame>, +t: Nat, e: FactDelivery,
  without: L.E<{Phases.absent(Phases.Complete{}, xs) == True{} : Bool}, {Phases.absent(Phases.Interrupted{}, xs) == True{} : Bool}>,
  query_result: {Q.query(xs, t) == Some{frame_delivery(e)} : Maybe<&2, Q.Frame>}) -> K.Rule7(fact_delivery(e), a, k, x, t):
  match e:
    case CompleteObserved{+bs}: L.ex_false(K.Rule7(I.DeliveredEverything{bs}, a, k, x, t),
      Phases.absent_excludes_query(Phases.Complete{}, xs, t, Q.Delivered{bs}, L.and_left(
        {Phases.absent(Phases.Complete{}, xs) == True{} : Bool}, {Phases.absent(Phases.Interrupted{}, xs) == True{} : Bool}, without), {==}, query_result))
    case PartialObserved{+bs}: L.ex_false(K.Rule7(I.DeliveryInterrupted{bs}, a, k, x, t),
      Phases.absent_excludes_query(Phases.Interrupted{}, xs, t, Q.Interrupted{bs}, L.and_right(
        {Phases.absent(Phases.Complete{}, xs) == True{} : Bool}, {Phases.absent(Phases.Interrupted{}, xs) == True{} : Bool}, without), {==}, query_result))

# The same suffix inversion decides complete, partial or absent delivery.
def delivery_in_suffix_obeys_rule7(-a: I.Environment, -k: String, -x: I.Scenario,
  +before: List<&2, Q.Frame>, +s: D.State, +r: S.Response, +bs: List<&2, U32>, +closure: Bool, +en: H.Delivery, +t: Nat, e: FactDelivery,
  without_complete: {Phases.absent(Phases.Complete{}, before) == True{} : Bool},
  without_partial: {Phases.absent(Phases.Interrupted{}, before) == True{} : Bool},
  prefix_real: PrefixOfWrite(N.Conclusion{s, r, bs}, en),
  query_result: {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, en)), t) == Some{frame_delivery(e)} : Maybe<&2, Q.Frame>},
  prepare: @u: Nat -> @rp: S.Response -> @bytes: List<&2, U32> ->
    {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, en)), u) == Some{Q.Prepared{rp, bytes}} : Maybe<&2, Q.Frame>} -> I.Happens(a, k, x, u, I.Prepared{rp, bytes}),
  conclude: @u: Nat -> @rp: S.Response -> @w: D.State -> @closes: Bool ->
    {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, en)), u) == Some{Q.Completed{rp, w, closes}} : Maybe<&2, Q.Frame>} -> I.Happens(a, k, x, u, I.Concluded{rp, w, closes}),
  complete: @u: Nat -> @bytes: List<&2, U32> -> I.Happens(a, k, x, u, I.DeliveredEverything{bytes}) ->
    {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, en)), u) == Some{Q.Delivered{bytes}} : Maybe<&2, Q.Frame>},
  partial: @u: Nat -> @bytes: List<&2, U32> -> I.Happens(a, k, x, u, I.DeliveryInterrupted{bytes}) ->
    {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, en)), u) == Some{Q.Interrupted{bytes}} : Maybe<&2, Q.Frame>},
  failure: @u: Nat -> @prefix: List<&2, U32> -> {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, en)), u) == Some{Q.Interrupted{prefix}} : Maybe<&2, Q.Frame>} -> I.FailureDeliveryReal(a, k, x, u)) ->
  K.Rule7(fact_delivery(e), a, k, x, t):
  match en:
    case H.Complete{+next}:
      match e:
        case CompleteObserved{other}:
          delivery_complete_reflected_obeys_rule7(a, k, x, before, s, r, bs, closure, next, t, other, query_result,
            without_complete, without_partial, prepare, conclude, complete, partial)
        case PartialObserved{+prefix}: L.ex_false(K.Rule7(I.DeliveryInterrupted{prefix}, a, k, x, t),
          Phases.absent_excludes_query(Phases.Interrupted{}, Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Complete{next})), t, Q.Interrupted{prefix},
            end_complete_without_interruption(before, s, r, bs, closure, next, without_partial), {==}, query_result))
    case H.Broken{+prefix}:
      match e:
        case CompleteObserved{+other}: L.ex_false(K.Rule7(I.DeliveredEverything{other}, a, k, x, t),
          Phases.absent_excludes_query(Phases.Complete{}, Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix})), t, Q.Delivered{other},
            end_partial_without_complete(before, s, r, bs, closure, prefix, without_complete), {==}, query_result))
        case PartialObserved{+other}:
          F.combined_pair(K.Rule7(I.DeliveryInterrupted{other}, a, k, x, t),
            {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix})), t) == Some{Q.Interrupted{other}} : Maybe<&2, Q.Frame>},
            {Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix})), t) == Some{Q.Interrupted{other}} : Maybe<&2, Q.Frame>},
            Call.duplicate_equality(Maybe<&2, Q.Frame>, Q.query(Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.Broken{prefix})), t), Some{Q.Interrupted{other}}, query_result),
            for_position => for_receipt => delivery_partial_reflected_obeys_rule7(a, k, x, before, s, r, bs, closure, prefix, t, other, for_position, prefix_real,
              failure(t, other, for_receipt), without_complete, without_partial, prepare, conclude, complete, partial))
    case H.PendingDelivery{}:
      match e:
        case CompleteObserved{+other}: L.ex_false(K.Rule7(I.DeliveredEverything{other}, a, k, x, t),
          Phases.absent_excludes_query(Phases.Complete{}, Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.PendingDelivery{})), t, Q.Delivered{other},
            before_of_delivery_without_mark(Phases.Complete{}, before, s, r, bs, closure, without_complete, {==}, {==}, {==}), {==}, query_result))
        case PartialObserved{+other}: L.ex_false(K.Rule7(I.DeliveryInterrupted{other}, a, k, x, t),
          Phases.absent_excludes_query(Phases.Interrupted{}, Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, H.PendingDelivery{})), t, Q.Interrupted{other},
            before_of_delivery_without_mark(Phases.Interrupted{}, before, s, r, bs, closure, without_partial, {==}, {==}, {==}), {==}, query_result))

def delivery_source_in_closure(~source: Source.Source, ~c: S.Configuration, +world: Nat, +initial: D.State, +rx: X.Reception,
  +before: List<&2, Q.Frame>, +s: D.State, +r: S.Response, +bs: List<&2, U32>, +closure: Bool, +en: H.Delivery, +t: Nat, +e: FactDelivery,
  canonical: {I.Serve{world, c, initial, rx} == Source.scenario(source, world) : I.Scenario},
  +same: {Vis.frames_call(c, initial, rx, Source.call(source, world)) == Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, en)) : List<&2, Q.Frame>},
  cleared: L.E<{Phases.absent(Phases.Complete{}, before) == True{} : Bool}, {Phases.absent(Phases.Interrupted{}, before) == True{} : Bool}>,
  prefix_real: PrefixOfWrite(N.Conclusion{s, r, bs}, en),
  failures: Channel.FailuresOfDeliveryReal(source, I.Serve{world, c, initial, rx}, Vis.frames_call(c, initial, rx, Source.call(source, world))),
  query_result: {Q.query(Vis.frames_call(c, initial, rx, Source.call(source, world)), t) == Some{frame_delivery(e)} : Maybe<&2, Q.Frame>}) ->
  K.Rule7(fact_delivery(e), Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, rx}, t):
  F.combined_pair(K.Rule7(fact_delivery(e), Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, rx}, t),
    {I.Serve{world, c, initial, rx} == Source.scenario(source, world) : I.Scenario}, {I.Serve{world, c, initial, rx} == Source.scenario(source, world) : I.Scenario},
    Call.duplicate_equality(I.Scenario, I.Serve{world, c, initial, rx}, Source.scenario(source, world), canonical),
    for_preparation => for_conclusion => F.combined_pair(K.Rule7(fact_delivery(e), Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, rx}, t),
      {Phases.absent(Phases.Complete{}, before) == True{} : Bool}, {Phases.absent(Phases.Interrupted{}, before) == True{} : Bool}, cleared,
      without_complete => without_partial => delivery_in_suffix_obeys_rule7(Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, rx},
        before, s, r, bs, closure, en, t, e, without_complete, without_partial, prefix_real,
        (%same : {Q.query(_, t) == Some{frame_delivery(e)} : Maybe<&2, Q.Frame>} query_result),
        +u => +rp => +bytes => obtained => Lig.introduce_in_list(source, c, world, initial, rx,
          Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, en)), u, Q.Prepared{rp, bytes}, I.Prepared{rp, bytes}, for_preparation, same, obtained, {==}, Unit{}),
        +u => +rp => +w => +closes => obtained => Lig.introduce_in_list(source, c, world, initial, rx,
          Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, en)), u, Q.Completed{rp, w, closes}, I.Concluded{rp, w, closes}, for_conclusion, same, obtained, {==}, Unit{}),
        +u => +bytes => fact => Lig.extract_in_list(source, c, world, initial, rx,
          Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, en)), u, I.DeliveredEverything{bytes}, same, Unit{}, fact),
        +u => +bytes => fact => Lig.extract_in_list(source, c, world, initial, rx,
          Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, en)), u, I.DeliveryInterrupted{bytes}, same, Unit{}, fact),
        +u => +bytes => obtained => failures(u, bytes,
          (%Equal.sym(List<&2, Q.Frame>, Vis.frames_call(c, initial, rx, Source.call(source, world)),
            Q.concatenate(before, H.render_conclusion(N.Conclusion{s, r, bs}, closure, en)), same) :
              {Q.query(_, u) == Some{Q.Interrupted{bytes}} : Maybe<&2, Q.Frame>} obtained)))))

def consume_delivery_selected(~source: Source.Source, ~c: S.Configuration, +world: Nat, +initial: D.State,
  +rx: X.Reception, +branch: H.Branch, q: Maybe<&2, Closures.Closure>, +t: Nat, +e: FactDelivery,
  canonical: {I.Serve{world, c, initial, rx} == Source.scenario(source, world) : I.Scenario},
  form: Closures.Form(Vis.frames_call(c, initial, rx, Source.call(source, world)), branch, q),
  cleared: Closures.DeliveriesOfForm(Vis.frames_call(c, initial, rx, Source.call(source, world)), q),
  prefix_real: PrefixesOfClosure(q),
  failures: Channel.FailuresOfDeliveryReal(source, I.Serve{world, c, initial, rx}, Vis.frames_call(c, initial, rx, Source.call(source, world))),
  query_result: {Q.query(Vis.frames_call(c, initial, rx, Source.call(source, world)), t) == Some{frame_delivery(e)} : Maybe<&2, Q.Frame>}) ->
  K.Rule7(fact_delivery(e), Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, rx}, t):
  match q:
    case None{}: delivery_without_closure_impossible(Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, rx},
      Vis.frames_call(c, initial, rx, Source.call(source, world)), t, e, cleared, query_result)
    case Some{Closures.Closure{before, N.Conclusion{w, r, bs}, closure, en, origin}}:
      match form:
        case L.Both{same_branch, L.Both{trace, L.Both{pub, concl}}}:
          delivery_source_in_closure(source, c, world, initial, rx, before, w, r, bs, closure, en, t, e, canonical, trace, cleared, prefix_real, failures, query_result)

def query_of_delivery(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception,
  +t: Nat, e: FactDelivery, obs: Source.of_route(source, I.Serve{world, c, s, rx}, t, fact_delivery(e))) ->
  {Q.query(Vis.frames_call(c, s, rx, Source.call(source, world)), t) == Some{frame_delivery(e)} : Maybe<&2, Q.Frame>}:
  match e:
    case CompleteObserved{+bs}: Lig.frame_of_observation(source, c, s, rx, Source.call(source, world), t, I.DeliveredEverything{bs}, Unit{}, obs)
    case PartialObserved{+bs}: Lig.frame_of_observation(source, c, s, rx, Source.call(source, world), t, I.DeliveryInterrupted{bs}, Unit{}, obs)

law delivery_of_call_obeys_rule7:
  for ~source: Source.Source
  for ~c: S.Configuration
  for +world: Nat
  for +initial: D.State
  for +rx: X.Reception
  for +t: Nat
  for +e: FactDelivery
  for prefix_real: PrefixesOfClosure(Closures.closure_of_branch(Lig.micro_of_data(Source.call(source, world)), initial, Lig.branch_of_data(c, rx, Source.call(source, world))))
  for failures: Channel.FailuresOfDeliveryReal(source, I.Serve{world, c, initial, rx}, Vis.frames_call(c, initial, rx, Source.call(source, world)))
  for observed: I.Happens(Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, rx}, t, fact_delivery(e))
  K.Rule7(fact_delivery(e), Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, rx}, t)
def delivery_of_call_obeys_rule7(source, c, world, initial, rx, t, e, prefix_real, failures, observed):
  F.combined_pair(K.Rule7(fact_delivery(e), Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, rx}, t),
    {Source.artifact(source) == Source.artifact(source) : String},
    L.E<{I.Serve{world, c, initial, rx} == Source.scenario(source, world) : I.Scenario}, Source.of_route(source, I.Serve{world, c, initial, rx}, t, fact_delivery(e))>,
    Source.eliminate_fact_literal(source, Source.artifact(source), I.Serve{world, c, initial, rx}, t, fact_delivery(e), observed),
    name => origin => F.combined_pair(K.Rule7(fact_delivery(e), Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, rx}, t),
      {I.Serve{world, c, initial, rx} == Source.scenario(source, world) : I.Scenario}, Source.of_route(source, I.Serve{world, c, initial, rx}, t, fact_delivery(e)), origin,
      canonical => obs => consume_delivery_selected(source, c, world, initial, rx, Lig.branch_of_data(c, rx, Source.call(source, world)),
        Closures.closure_of_branch(Lig.micro_of_data(Source.call(source, world)), initial, Lig.branch_of_data(c, rx, Source.call(source, world))), t, e, canonical,
        (%Equal.sym(List<&2, Q.Frame>, Vis.frames_call(c, initial, rx, Source.call(source, world)),
          H.render(Lig.micro_of_data(Source.call(source, world)), initial, Lig.branch_of_data(c, rx, Source.call(source, world))),
          Lig.frames_follow_o_branch(c, initial, rx, Source.call(source, world))) : Closures.Form(_, Lig.branch_of_data(c, rx, Source.call(source, world)),
            Closures.closure_of_branch(Lig.micro_of_data(Source.call(source, world)), initial, Lig.branch_of_data(c, rx, Source.call(source, world))))
          Closures.form_of_route(Lig.micro_of_data(Source.call(source, world)), initial, Lig.branch_of_data(c, rx, Source.call(source, world)))),
        (%Equal.sym(List<&2, Q.Frame>, Vis.frames_call(c, initial, rx, Source.call(source, world)),
          H.render(Lig.micro_of_data(Source.call(source, world)), initial, Lig.branch_of_data(c, rx, Source.call(source, world))),
          Lig.frames_follow_o_branch(c, initial, rx, Source.call(source, world))) : Closures.DeliveriesOfForm(_,
            Closures.closure_of_branch(Lig.micro_of_data(Source.call(source, world)), initial, Lig.branch_of_data(c, rx, Source.call(source, world))))
          Closures.deliveries_of_form(Lig.micro_of_data(Source.call(source, world)), initial, Lig.branch_of_data(c, rx, Source.call(source, world)))),
        prefix_real, failures, query_of_delivery(source, c, world, initial, rx, t, e, obs))))


# Only the actual input branch has an envelope-rejection obligation.
def InputOfBranch(~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception, branch: H.Branch) -> Type:
  match branch:
    case H.InputRefusal{error, closes, en}: Causes.CauseInput(I.Serve{world, c, s, rx}, error)
    case _: Unit

def without_input_has_cause(~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception, branch: H.Branch,
  negative: {is_input(branch) == False{} : Bool}) -> InputOfBranch(c, world, s, rx, branch):
  match branch:
    case H.InputRefusal{+error, closes, en}: L.ex_false(Causes.CauseInput(I.Serve{world, c, s, rx}, error), F.false_negative_true(Equal.sym(Bool, True{}, False{}, negative)))
    case H.AutRefusal{r, en}: Unit{}
    case H.GateRefusal{r, ctx, en}: Unit{}
    case H.Executed{r, ctx, qs, p, en}: Unit{}
    case H.FailureBefore{phase, stage, id, fatal, en}: Unit{}
    case H.InitialOk{}: Unit{}
    case H.InitialRefusal{status}: Unit{}
    case H.InitialFailure{accepts, stage, id, fatal}: Unit{}
    case H.WithoutResponse{}: Unit{}
    case H.FatalAfterPublication{r, ctx, qs, p, stage, id}: Unit{}
    case H.Pending{phase}: Unit{}
    case H.InitialPending{accepts}: Unit{}

# Parameters are actual measures and bytes, not an InputInvalid hypothesis.
def CopyOfBody(~c: S.Configuration, +s: D.State, +rx: X.Reception, +be: List<&2, U32>, +br: List<&2, U32>, +bs: List<&2, U32>) -> Type:
  L.E<Causes.StateCopied(c, s, be), L.E<Causes.BodyCopied(c, rx),
    L.E<{Transport.join(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>},
      L.E<{B.octets_all_valid(br) == True{} : Bool},
        L.E<{D.structure(S.schema(c), s) == True{} : Bool},
          {X.decide_reception(c, rx) == X.ProcessBody{br} : X.Disposition}>>>>>

def cause_combined_measures_of_body(~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception,
  +be: List<&2, U32>, +br: List<&2, U32>, +bs: List<&2, U32>, +status: S.Status, +ce: B.Number64, +te: B.Number64,
  cod_and: P.Encoding(D.state_value(s), be), assembly: {Transport.join(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>},
  measure_and: {B.nat64(B.length(be)) == Some{ce} : Maybe<&2, B.Number64>}, ceiling_and: {B.nat64(R.limit_state(S.limits(c))) == Some{te} : Maybe<&2, B.Number64>},
  fits_and: {Codec.less_equal64(ce, te) == True{} : Bool}, octets_r: {B.octets_all_valid(br) == True{} : Bool},
  structure: {D.structure(S.schema(c), s) == True{} : Bool}, received: {X.decide_reception(c, rx) == X.ProcessBody{br} : X.Disposition},
  real: {Input.decode(bs, S.schema(c), S.limits(c)) == Input.ErrorMessage{status} : Input.PreAuthentication},
  measures: &cr: B.Number64 -> &tr: B.Number64 -> L.E<{B.nat64(B.length(br)) == Some{cr} : Maybe<&2, B.Number64>},
    L.E<{B.nat64(R.limit_message(S.limits(c))) == Some{tr} : Maybe<&2, B.Number64>}, {Codec.less_equal64(cr, tr) == True{} : Bool}>>) ->
  Causes.CauseInput(I.Serve{world, c, s, rx}, H.error_of_message(status)):
  match measures:
    case (+cr, +tr, L.Both{measure_r, L.Both{ceiling_r, fits_r}}):
      +canon_and = {cod_and : {P.encode(D.state_value(s)) == Some{be} : Maybe<&2, List<&2, U32>>}}
      Causes.error_of_body_processed_has_cause_original(c, world, s, rx, be, br, bs, ce, cr, te, tr, status,
        canon_and, assembly, Octets.any_encoding_only_emits_octets(D.state_value(s), be, canon_and), octets_r,
        measure_and, measure_r, ceiling_and, ceiling_r, fits_and, fits_r, structure, received, real)

def cause_by_copy(~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception,
  +be: List<&2, U32>, +br: List<&2, U32>, +bs: List<&2, U32>, +status: S.Status, copy: CopyOfBody(c, s, rx, be, br, bs),
  real: {Input.decode(bs, S.schema(c), S.limits(c)) == Input.ErrorMessage{status} : Input.PreAuthentication}) ->
  Causes.CauseInput(I.Serve{world, c, s, rx}, H.error_of_message(status)):
  match copy:
    case L.Both{(+ce, +te, L.Both{cod_and, L.Both{measure_and, L.Both{ceiling_and, fits_and}}}),
      L.Both{L.Both{reception_is_valid, measure}, L.Both{assembly, L.Both{octets_r, L.Both{structure, +received}}}}}:
      cause_combined_measures_of_body(c, world, s, rx, be, br, bs, status, ce, te, cod_and, assembly,
        measure_and, ceiling_and, fits_and, octets_r, structure, received, real, measure(br, received))

def pre_has_cause(~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception,
  +be: List<&2, U32>, +br: List<&2, U32>, +bs: List<&2, U32>, pre: Input.PreAuthentication, +data: H.DataTools,
  copy: CopyOfBody(c, s, rx, be, br, bs), real: {Input.decode(bs, S.schema(c), S.limits(c)) == pre : Input.PreAuthentication}) ->
  InputOfBranch(c, world, s, rx, H.decide_pre(pre, data)):
  match pre:
    case Input.InputReady{+decoded, +r}: without_input_has_cause(c, world, s, rx, H.decide_authentication(H.preprocessing(data), decoded, r, data),
      authentication_negative_and_input(H.preprocessing(data), decoded, r, data))
    case Input.ErrorMessage{+status}:
      match data:
        case H.DataTools{j, ex, li, en, pipe}: cause_by_copy(c, world, s, rx, be, br, bs, status, copy, real)
    case Input.ErrorTransport{}:
      match data:
        case H.DataTools{j, ex, li, en, pipe}: Unit{}

def decode_has_cause(~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception,
  +be: List<&2, U32>, +br: List<&2, U32>, +bs: List<&2, U32>, pre: H.Preprocessing, data: H.DataTools,
  copy: CopyOfBody(c, s, rx, be, br, bs)) -> InputOfBranch(c, world, s, rx, H.decide_decode(pre, bs, S.schema(c), S.limits(c), data)):
  match pre:
    case H.FailureDecode{id, fatal}: Unit{}
    case H.PendingDecode{}: Unit{}
    case H.Normal{}: pre_has_cause(c, world, s, rx, be, br, bs, Input.decode(bs, S.schema(c), S.limits(c)), data, copy, {==})
    case H.FailureFraming{id, fatal}: pre_has_cause(c, world, s, rx, be, br, bs, Input.decode(bs, S.schema(c), S.limits(c)), data, copy, {==})
    case H.FailureAuth{id, fatal}: pre_has_cause(c, world, s, rx, be, br, bs, Input.decode(bs, S.schema(c), S.limits(c)), data, copy, {==})
    case H.PendingFraming{}: pre_has_cause(c, world, s, rx, be, br, bs, Input.decode(bs, S.schema(c), S.limits(c)), data, copy, {==})
    case H.PendingAuth{}: pre_has_cause(c, world, s, rx, be, br, bs, Input.decode(bs, S.schema(c), S.limits(c)), data, copy, {==})

def packet_has_cause(~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception,
  +be: List<&2, U32>, +br: List<&2, U32>, packet: Maybe<&2, List<&2, U32>>, +data: H.DataTools,
  state: Causes.StateCopied(c, s, be), body: Causes.BodyCopied(c, rx),
  octets_r: {B.octets_all_valid(br) == True{} : Bool}, structure: {D.structure(S.schema(c), s) == True{} : Bool},
  received: {X.decide_reception(c, rx) == X.ProcessBody{br} : X.Disposition},
  assembly: {Transport.join(be, br) == packet : Maybe<&2, List<&2, U32>>}) ->
  InputOfBranch(c, world, s, rx, H.decide_packet(packet, S.schema(c), S.limits(c), data)):
  match packet:
    case None{}:
      match data:
        case H.DataTools{j, ex, li, en, pipe}: Unit{}
    case Some{+bs}: decode_has_cause(c, world, s, rx, be, br, bs, H.preprocessing(data), data,
      L.Both{state, L.Both{body, L.Both{assembly, L.Both{octets_r, L.Both{structure, received}}}}})

# The actual header can reject only Input and Limit statuses.
def StatusOfHeader(status: S.Status) -> Type:
  match status:
    case S.Input{}: Unit
    case S.Limit{}: Unit
    case _: Empty

def HeaderReal(d: X.Disposition) -> Type:
  match d:
    case X.RefuseClose{status}: StatusOfHeader(status)
    case X.RefuseContinue{status}: Empty
    case _: Unit

def header_truncated_real(above: Bool) -> HeaderReal(X.truncated_cases(above)):
  match above:
    case False{}: Unit{}
    case True{}: Unit{}

def header_complete_real(above: Bool, br: List<&2, U32>) -> HeaderReal(X.complete_cases(above, br)):
  match above:
    case False{}: Unit{}
    case True{}: Unit{}

def reception_has_header_real(~c: S.Configuration, rx: X.Reception) -> HeaderReal(X.decide_reception(c, rx)):
  match rx:
    case X.EOFBetweenMessages{}: Unit{}
    case X.StoppedOperator{}: Unit{}
    case X.HeaderTruncated{bs}: Unit{}
    case X.BodyTruncated{a, b, bs}: header_truncated_real(X.declared_greater(a, b, R.limit_message(S.limits(c))))
    case X.BodyReceived{a, b, bs}: header_complete_real(X.declared_greater(a, b, R.limit_message(S.limits(c))), bs)

def disposition_has_cause(~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception,
  +be: List<&2, U32>, +d: X.Disposition, +data: H.DataTools,
  state: Causes.StateCopied(c, s, be), body: Causes.BodyCopied(c, rx),
  octets_r: Two.OctetsReceived(d), structure: {D.structure(S.schema(c), s) == True{} : Bool},
  header: HeaderReal(d), received: {X.decide_reception(c, rx) == d : X.Disposition}) ->
  InputOfBranch(c, world, s, rx, H.decide_disposition(d, be, S.schema(c), S.limits(c), data)):
  match d:
    case X.CloseWithoutResponse{}: Unit{}
    case X.RefuseClose{status}:
      match status:
        case S.Input{}:
          match data:
            case H.DataTools{j, ex, li, en, pre}: L.Left{L.Left{received}}
        case S.Limit{}:
          match data:
            case H.DataTools{j, ex, li, en, pre}: received
        case S.Success{}: match header:
        case S.Refusal{}: match header:
        case S.Authentication{}: match header:
        case S.Certificate{}: match header:
        case S.DataError{}: match header:
        case S.Failure{}: match header:
    case X.RefuseContinue{+status}: L.ex_false(InputOfBranch(c, world, s, rx, H.decide_disposition(X.RefuseContinue{status}, be, S.schema(c), S.limits(c), data)), header)
    case X.ProcessBody{+br}: packet_has_cause(c, world, s, rx, be, br, Transport.join(be, br), data,
      state, body, octets_r, structure, received, {==})

def framing_has_cause(~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception,
  +be: List<&2, U32>, pre: H.Preprocessing, +d: X.Disposition, +data: H.DataTools,
  state: Causes.StateCopied(c, s, be), body: Causes.BodyCopied(c, rx),
  octets_r: Two.OctetsReceived(d), structure: {D.structure(S.schema(c), s) == True{} : Bool},
  header: HeaderReal(d), received: {X.decide_reception(c, rx) == d : X.Disposition}) ->
  InputOfBranch(c, world, s, rx, H.decide_framing(pre, d, be, S.schema(c), S.limits(c), data)):
  match pre:
    case H.FailureFraming{id, fatal}: Unit{}
    case H.PendingFraming{}: Unit{}
    case H.Normal{}: disposition_has_cause(c, world, s, rx, be, d, data, state, body, octets_r, structure, header, received)
    case H.FailureDecode{id, fatal}: disposition_has_cause(c, world, s, rx, be, d, data, state, body, octets_r, structure, header, received)
    case H.FailureAuth{id, fatal}: disposition_has_cause(c, world, s, rx, be, d, data, state, body, octets_r, structure, header, received)
    case H.PendingDecode{}: disposition_has_cause(c, world, s, rx, be, d, data, state, body, octets_r, structure, header, received)
    case H.PendingAuth{}: disposition_has_cause(c, world, s, rx, be, d, data, state, body, octets_r, structure, header, received)

law input_of_decision_has_cause_original:
  for ~c: S.Configuration
  for +world: Nat
  for +s: D.State
  for +rx: X.Reception
  for +be: List<&2, U32>
  for +data: H.DataTools
  for state: Causes.StateCopied(c, s, be)
  for body: Causes.BodyCopied(c, rx)
  for octets_r: Two.OctetsReceived(X.decide_reception(c, rx))
  for structure: {D.structure(S.schema(c), s) == True{} : Bool}
  InputOfBranch(c, world, s, rx, H.decide(c, rx, be, data))
def input_of_decision_has_cause_original(c, world, s, rx, be, data, state, body, octets_r, structure):
  %Equal.sym(H.Branch, H.decide(c, rx, be, data), H.decide_framing(H.preprocessing(data), X.decide_reception(c, rx), be, S.schema(c), S.limits(c), data),
    Two.decide_by_reception(c, rx, be, data)) : InputOfBranch(c, world, s, rx, _)
  framing_has_cause(c, world, s, rx, be, H.preprocessing(data), X.decide_reception(c, rx), data,
    state, body, octets_r, structure, reception_has_header_real(c, rx), {==})


# The last evaluation belongs to the physical prefix preceding prepare.
def prefix_of_execution_grouped(+m: H.Micro, +req: P.Request, +ctx: D.Context, +xs: List<&2, Q.FrameExec>) ->
  {Con{Q.Configured{}, Closures.before_execution(m, req, ctx, xs)} ==
    Law5.subtrace(Con{Q.Configured{}, H.render_started(m, req, ctx)}, Q.expand_exec(req, ctx, xs), H.micro_output(m)) : List<&2, Q.Frame>}:
  Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, ys => Con{Q.Configured{}, ys},
    Q.concatenate(Q.concatenate(H.render_started(m, req, ctx), Q.expand_exec(req, ctx, xs)), H.micro_output(m)),
    Q.concatenate(H.render_started(m, req, ctx), Q.concatenate(Q.expand_exec(req, ctx, xs), H.micro_output(m))),
    Q.concatenate_assoc(H.render_started(m, req, ctx), Q.expand_exec(req, ctx, xs), H.micro_output(m)))

def evaluation_in_prefix_native(+m: H.Micro, +req: P.Request, +ctx: D.Context, +xs: List<&2, Q.FrameExec>,
  +w: D.State, +ts: List<&2, S.OperationEvent>, +proposal: S.Response,
  index: &i: Nat -> {Exec.query(xs, i) == Some{Q.Evaluation{S.Final{w, ts, proposal}}} : Maybe<&2, Q.FrameExec>}) ->
  &u: Nat -> {Q.query(Con{Q.Configured{}, Closures.before_execution(m, req, ctx, xs)}, u) == Some{Q.Evaluated{req, ctx, S.Final{w, ts, proposal}}} : Maybe<&2, Q.Frame>}:
  match index:
    case (+i, present):
      (Nat.add(Q.size(Con{Q.Configured{}, H.render_started(m, req, ctx)}), i),
        Equal.trans(Maybe<&2, Q.Frame>,
          Q.query(Con{Q.Configured{}, Closures.before_execution(m, req, ctx, xs)}, Nat.add(Q.size(Con{Q.Configured{}, H.render_started(m, req, ctx)}), i)),
          Q.query(Law5.subtrace(Con{Q.Configured{}, H.render_started(m, req, ctx)}, Q.expand_exec(req, ctx, xs), H.micro_output(m)), Nat.add(Q.size(Con{Q.Configured{}, H.render_started(m, req, ctx)}), i)),
          Some{Q.Evaluated{req, ctx, S.Final{w, ts, proposal}}},
          Equal.cong(List<&2, Q.Frame>, Maybe<&2, Q.Frame>, ys => Q.query(ys, Nat.add(Q.size(Con{Q.Configured{}, H.render_started(m, req, ctx)}), i)),
            Con{Q.Configured{}, Closures.before_execution(m, req, ctx, xs)},
            Law5.subtrace(Con{Q.Configured{}, H.render_started(m, req, ctx)}, Q.expand_exec(req, ctx, xs), H.micro_output(m)), prefix_of_execution_grouped(m, req, ctx, xs)),
          Law5.query_of_subtrace(Con{Q.Configured{}, H.render_started(m, req, ctx)}, Q.expand_exec(req, ctx, xs), H.micro_output(m), i, Q.Evaluated{req, ctx, S.Final{w, ts, proposal}},
            Exec.expand_preserves_query(req, ctx, xs, i, Q.Evaluation{S.Final{w, ts, proposal}}, present))))

def preparation_code_combined_fields_real(~source: Source.Source, ~c: S.Configuration,
  -a: I.Environment, -k: String, -x: I.Scenario, +m: H.Micro, +before: List<&2, Q.Frame>, +later: List<&2, Q.Frame>,
  +s: D.State, +req: P.Request, +ctx: D.Context, +code: Source.JudgmentSyntactic, +xs: List<&2, Q.FrameExec>,
  +n: Nat, +w: D.State, +ts: List<&2, S.OperationEvent>, +proposal: S.Response, +r: S.Response, +bs: List<&2, U32>,
  prefix: {before == Con{Q.Configured{}, Closures.before_execution(m, req, ctx, xs)} : List<&2, Q.Frame>},
  sequence: {xs == Exec.generate(n, N.start(Source.program(source, code), ctx, I.arguments(req), s), S.schema(c)) : List<&2, Q.FrameExec>},
  +result: {N.traverse(n, N.start(Source.program(source, code), ctx, I.arguments(req), s), S.schema(c)) == S.Final{w, ts, proposal} : S.Trace},
  obtained: {N.prepare(N.Stopped{w, ts, proposal}, c) == Some{N.Prepared{w, ts, r, bs}} : Maybe<&2, N.Prepared>},
  configuration: {I.configuration(x) == c : S.Configuration}, is_valid: {R.configuration_is_valid(c) == True{} : Bool},
  evaluate: @u: Nat -> {Q.query(Q.concatenate(before, Con{Q.Prepared{r, bs}, later}), u) == Some{Q.Evaluated{req, ctx, S.Final{w, ts, proposal}}} : Maybe<&2, Q.Frame>} ->
    I.Happens(a, k, x, u, I.Evaluated{req, ctx, Source.program(source, code), S.Final{w, ts, proposal}})) ->
  K.Rule7(I.Prepared{r, bs}, a, k, x, Nat.add(Q.size(before), 0n)):
  preparation_of_program_obeys_rule7(source, c, a, k, x, before, Con{Q.Prepared{r, bs}, later}, s, req, ctx, code, n, w, ts, proposal, r, bs,
    configuration, is_valid, obtained, result,
    (%Equal.sym(List<&2, Q.Frame>, before, Con{Q.Configured{}, Closures.before_execution(m, req, ctx, xs)}, prefix) :
      (&u: Nat -> {Q.query(_, u) == Some{Q.Evaluated{req, ctx, S.Final{w, ts, proposal}}} : Maybe<&2, Q.Frame>})
      evaluation_in_prefix_native(m, req, ctx, xs, w, ts, proposal, last_evaluation_of_result_real(source, c, s, req, ctx, code, n, w, ts, proposal, xs, sequence, result))), evaluate)

def working_prepared(p: N.Prepared) -> D.State:
  match p:
    case N.Prepared{w, ts, r, bs}: w

def events_prepared(p: N.Prepared) -> List<&2, S.OperationEvent>:
  match p:
    case N.Prepared{w, ts, r, bs}: ts

def fields_normalized_prepared(+wp: D.State, +tsp: List<&2, S.OperationEvent>, +rp: S.Response, +bs: List<&2, U32>,
  +w: D.State, +ts: List<&2, S.OperationEvent>, +r: S.Response,
  +equal: {N.Prepared{wp, tsp, rp, bs} == N.Prepared{w, ts, r, bs} : N.Prepared}) ->
  L.E<{wp == w : D.State}, {tsp == ts : List<&2, S.OperationEvent>}>:
  L.Both{Equal.cong(N.Prepared, D.State, working_prepared, N.Prepared{wp, tsp, rp, bs}, N.Prepared{w, ts, r, bs}, equal),
    Equal.cong(N.Prepared, List<&2, S.OperationEvent>, events_prepared, N.Prepared{wp, tsp, rp, bs}, N.Prepared{w, ts, r, bs}, equal)}

def preparation_code_reindexed(~source: Source.Source, ~c: S.Configuration,
  -a: I.Environment, -k: String, -x: I.Scenario, +m: H.Micro, +before: List<&2, Q.Frame>, +later: List<&2, Q.Frame>,
  +s: D.State, +req: P.Request, +ctx: D.Context, +code: Source.JudgmentSyntactic, +xs: List<&2, Q.FrameExec>,
  +n: Nat, +w: D.State, +ts: List<&2, S.OperationEvent>, +proposal: S.Response,
  +wp: D.State, +tsp: List<&2, S.OperationEvent>, +rp: S.Response, +bs: List<&2, U32>,
  prefix: {before == Con{Q.Configured{}, Closures.before_execution(m, req, ctx, xs)} : List<&2, Q.Frame>},
  sequence: {xs == Exec.generate(n, N.start(Source.program(source, code), ctx, I.arguments(req), s), S.schema(c)) : List<&2, Q.FrameExec>},
  result: {N.traverse(n, N.start(Source.program(source, code), ctx, I.arguments(req), s), S.schema(c)) == S.Final{w, ts, proposal} : S.Trace},
  obtained: {N.prepare(N.Stopped{w, ts, proposal}, c) == Some{N.Prepared{wp, tsp, rp, bs}} : Maybe<&2, N.Prepared>},
  configuration: {I.configuration(x) == c : S.Configuration}, is_valid: {R.configuration_is_valid(c) == True{} : Bool},
  evaluate: @u: Nat -> {Q.query(Q.concatenate(before, Con{Q.Prepared{rp, bs}, later}), u) == Some{Q.Evaluated{req, ctx, S.Final{wp, tsp, proposal}}} : Maybe<&2, Q.Frame>} ->
    I.Happens(a, k, x, u, I.Evaluated{req, ctx, Source.program(source, code), S.Final{wp, tsp, proposal}}),
  fields: L.E<{wp == w : D.State}, {tsp == ts : List<&2, S.OperationEvent>}>) -> K.Rule7(I.Prepared{rp, bs}, a, k, x, Nat.add(Q.size(before), 0n)):
  match fields:
    case L.Both{+state, +events}:
      preparation_code_combined_fields_real(source, c, a, k, x, m, before, later, s, req, ctx, code, xs, n, wp, tsp, proposal, rp, bs, prefix, sequence,
        (%Equal.sym(D.State, wp, w, state) : {N.traverse(n, N.start(Source.program(source, code), ctx, I.arguments(req), s), S.schema(c)) == S.Final{_, tsp, proposal} : S.Trace}
          %Equal.sym(List<&2, S.OperationEvent>, tsp, ts, events) : {N.traverse(n, N.start(Source.program(source, code), ctx, I.arguments(req), s), S.schema(c)) == S.Final{w, _, proposal} : S.Trace} result),
        (%Equal.sym(D.State, wp, w, state) : {N.prepare(N.Stopped{_, tsp, proposal}, c) == Some{N.Prepared{wp, tsp, rp, bs}} : Maybe<&2, N.Prepared>}
          %Equal.sym(List<&2, S.OperationEvent>, tsp, ts, events) : {N.prepare(N.Stopped{w, _, proposal}, c) == Some{N.Prepared{wp, tsp, rp, bs}} : Maybe<&2, N.Prepared>} obtained), configuration, is_valid, evaluate)

def preparation_code_of_final_real(~source: Source.Source, ~c: S.Configuration,
  -a: I.Environment, -k: String, -x: I.Scenario, +m: H.Micro, +before: List<&2, Q.Frame>, +later: List<&2, Q.Frame>,
  +s: D.State, +req: P.Request, +ctx: D.Context, +code: Source.JudgmentSyntactic, +xs: List<&2, Q.FrameExec>, p: N.Prepared,
  prefix: {before == Con{Q.Configured{}, Closures.before_execution(m, req, ctx, xs)} : List<&2, Q.Frame>},
  real: Source.FinalReal(source, c, s, req, ctx, code, xs, p),
  configuration: {I.configuration(x) == c : S.Configuration}, is_valid: {R.configuration_is_valid(c) == True{} : Bool},
  evaluate: @u: Nat -> @w: D.State -> @ts: List<&2, S.OperationEvent> -> @proposal: S.Response ->
    {Q.query(Q.concatenate(before, Con{H.frame_prepared(p), later}), u) == Some{Q.Evaluated{req, ctx, S.Final{w, ts, proposal}}} : Maybe<&2, Q.Frame>} ->
      I.Happens(a, k, x, u, I.Evaluated{req, ctx, Source.program(source, code), S.Final{w, ts, proposal}})) ->
  K.Rule7(I.Prepared{U.response(p), Preparation.bytes_prepared(p)}, a, k, x, Nat.add(Q.size(before), 0n)):
  match p:
    case N.Prepared{+wp, +tsp, +rp, +bs}:
      match real:
        case (+n, +w, +ts, +proposal, L.Both{sequence, L.Both{result, +obtained}}):
          preparation_code_reindexed(source, c, a, k, x, m, before, later, s, req, ctx, code, xs, n, w, ts, proposal, wp, tsp, rp, bs,
            prefix, sequence, result, obtained, configuration, is_valid, +u => query_result => evaluate(u, wp, tsp, proposal, query_result),
            fields_normalized_prepared(wp, tsp, rp, bs, w, ts, R.finalize(proposal, c, w),
              L.and_left(
                {N.Prepared{wp, tsp, rp, bs} == N.Prepared{w, ts, R.finalize(proposal, c, w), bs} : N.Prepared},
                P.Message(S.response_value(R.finalize(proposal, c, w)), bs),
                normalize_prepared_real(c, w, ts, proposal, N.Prepared{wp, tsp, rp, bs}, obtained))))


def fact_preparation(q: Q.Frame) -> I.Fact:
  match q:
    case Q.Prepared{r, bs}: I.Prepared{r, bs}
    case _: I.ProofInitialAccepts{}

def transport_preparation7(-a: I.Environment, -k: String, -x: I.Scenario, +before: List<&2, Q.Frame>, -t: Nat,
  +r: S.Response, +bs: List<&2, U32>, +q: Q.Frame,
  pos: {t == Nat.add(Q.size(before), 0n) : Nat}, equal: {Q.Prepared{r, bs} == q : Q.Frame},
  canonical: K.Rule7(fact_preparation(q), a, k, x, Nat.add(Q.size(before), 0n))) -> K.Rule7(I.Prepared{r, bs}, a, k, x, t):
  %Equal.sym(Nat, t, Nat.add(Q.size(before), 0n), pos) : K.Rule7(I.Prepared{r, bs}, a, k, x, _)
  %Equal.sym(Q.Frame, Q.Prepared{r, bs}, q, equal) : K.Rule7(fact_preparation(_), a, k, x, Nat.add(Q.size(before), 0n))
  canonical

# This function chooses no alternative program: the root belongs to the same source.
def preparation_native_of_source(~source: Source.Source, ~c: S.Configuration, +world: Nat, +initial: D.State, +rx: X.Reception,
  +m: H.Micro, +before: List<&2, Q.Frame>, +later: List<&2, Q.Frame>, +req: P.Request, +ctx: D.Context,
  +code: Source.JudgmentSyntactic, +xs: List<&2, Q.FrameExec>, +p: N.Prepared,
  canonical: {I.Serve{world, c, initial, rx} == Source.scenario(source, world) : I.Scenario},
  +trace: {Vis.frames_call(c, initial, rx, Source.call(source, world)) == Q.concatenate(before, Con{H.frame_prepared(p), later}) : List<&2, Q.Frame>},
  prefix: {before == Con{Q.Configured{}, Closures.before_execution(m, req, ctx, xs)} : List<&2, Q.Frame>},
  real: Source.FinalReal(source, c, initial, req, ctx, code, xs, p), is_valid: {R.configuration_is_valid(c) == True{} : Bool},
  same_root: {Source.program(source, code) == Law5.program_of_world(source, world) : S.Program}) ->
  K.Rule7(I.Prepared{U.response(p), Preparation.bytes_prepared(p)}, Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, rx}, Nat.add(Q.size(before), 0n)):
  preparation_code_of_final_real(source, c, Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, rx}, m, before, later,
    initial, req, ctx, code, xs, p, prefix, real, {==}, is_valid,
    +u => +w => +ts => +proposal => query_result =>
      (%Equal.sym(S.Program, Source.program(source, code), Law5.program_of_world(source, world), same_root) :
        I.Happens(Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, rx}, u, I.Evaluated{req, ctx, _, S.Final{w, ts, proposal}})
        Lig.introduce_in_list(source, c, world, initial, rx, Q.concatenate(before, Con{H.frame_prepared(p), later}), u,
          Q.Evaluated{req, ctx, S.Final{w, ts, proposal}}, I.Evaluated{req, ctx, Law5.program_of_world(source, world), S.Final{w, ts, proposal}},
          canonical, trace, query_result, {==}, Unit{})))

def fact_causal(q: Q.Frame) -> I.Fact:
  match q:
    case Q.Authenticated{r, ctx}: I.Authenticated{r, ctx}
    case Q.Rejected{r, ctx}: I.CertificateRejected{r, ctx}
    case Q.Failed{stage, id, fatal}: I.FailedEnvironment{stage, id, fatal}
    case _: I.ProofInitialAccepts{}

def frame_causal_of_prefix(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception,
  +before: List<&2, Q.Frame>, +later: List<&2, Q.Frame>, +u: Nat, +q: Q.Frame,
  canonical: {I.Serve{world, c, s, rx} == Source.scenario(source, world) : I.Scenario},
  trace: {Vis.frames_call(c, s, rx, Source.call(source, world)) == Q.concatenate(before, later) : List<&2, Q.Frame>},
  +present: {Q.query(before, u) == Some{q} : Maybe<&2, Q.Frame>},
  relation: Q.rel_fact(c, Law5.program_of_world(source, world), q, fact_causal(q)), milestone: Lig.Milestone(fact_causal(q))) ->
  I.Before(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, Nat.add(Q.size(before), 0n), fact_causal(q)):
  (u, L.Both{less_that_sum_by_right(u, Q.size(before), 0n, Q.position_present_inside(before, u, q, present)),
    Lig.introduce_in_list(source, c, world, s, rx, Q.concatenate(before, later), u, q, fact_causal(q), canonical, trace,
      Adm.query_prefix(before, later, u, q, present), relation, milestone)})

# The fixed origin retained by inversion excludes a cause from another branch.
def cause_fixed_of_branch(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception,
  +m: H.Micro, +before: List<&2, Q.Frame>, +later: List<&2, Q.Frame>, +e: Errors.Error, branch: H.Branch,
  canonical: {I.Serve{world, c, s, rx} == Source.scenario(source, world) : I.Scenario},
  trace: {Vis.frames_call(c, s, rx, Source.call(source, world)) == Q.concatenate(before, later) : List<&2, Q.Frame>},
  origin: Closures.FixedOfBranch(e, branch), prefix: Closures.PrefixFixed(m, branch, before),
  input: InputOfBranch(c, world, s, rx, branch), command: Source.RequestOfBranch(c, Source.Service{world, s, rx}, branch)) ->
  I.ResponseJustified(S.response_error(Errors.status(e)), Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, Nat.add(Q.size(before), 0n)):
  match branch:
    case H.InputRefusal{H.Input{}, closes, en}:
      %Equal.sym(Errors.Error, e, Errors.Input{}, origin) :
        I.ResponseJustified(S.response_error(Errors.status(_)), Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, Nat.add(Q.size(before), 0n))
      input
    case H.InputRefusal{H.Limit{}, closes, en}:
      %Equal.sym(Errors.Error, e, Errors.Limit{}, origin) :
        I.ResponseJustified(S.response_error(Errors.status(_)), Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, Nat.add(Q.size(before), 0n))
      L.Left{input}
    case H.AutRefusal{+req, en}:
      %Equal.sym(Errors.Error, e, Errors.Authentication{}, origin) :
        I.ResponseJustified(S.response_error(Errors.status(_)), Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, Nat.add(Q.size(before), 0n))
      (req, L.Both{frame_causal_of_prefix(source, c, world, s, rx, before, later, Adm.index_auth(m, req), Q.Authenticated{req, None{}},
        canonical, trace,
        (%Equal.sym(List<&2, Q.Frame>, before, Con{Q.Configured{}, Closures.before_authentication(m, req)}, prefix) :
          {Q.query(_, Adm.index_auth(m, req)) == Some{Q.Authenticated{req, None{}}} : Maybe<&2, Q.Frame>} Adm.query_auth(m, req, None{})), {==}, Unit{}), command})
    case H.GateRefusal{+req, +ctx, en}:
      %Equal.sym(Errors.Error, e, Errors.Certificate{}, origin) :
        I.ResponseJustified(S.response_error(Errors.status(_)), Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, Nat.add(Q.size(before), 0n))
      (req, ctx, frame_causal_of_prefix(source, c, world, s, rx, before, later,
        Nat.add(Q.size(Con{Q.Configured{}, H.render_authenticated(m, req, ctx)}), 0n), Q.Rejected{req, ctx}, canonical, trace,
        (%Equal.sym(List<&2, Q.Frame>, before, Con{Q.Configured{}, Closures.before_gate(m, req, ctx)}, prefix) :
          {Q.query(_, Nat.add(Q.size(Con{Q.Configured{}, H.render_authenticated(m, req, ctx)}), 0n)) == Some{Q.Rejected{req, ctx}} : Maybe<&2, Q.Frame>}
          Adm.query_of_mark(Con{Q.Configured{}, H.render_authenticated(m, req, ctx)}, Q.Rejected{req, ctx})), {==}, Unit{}))
    case H.FailureBefore{+phase, +stage, +id, +fatal, en}:
      match origin:
        case L.Both{equal, negative_fatal}:
          %Equal.sym(Errors.Error, e, Errors.Failure{}, equal) :
            I.ResponseJustified(S.response_error(Errors.status(_)), Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, Nat.add(Q.size(before), 0n))
          (stage, id, fatal, frame_causal_of_prefix(source, c, world, s, rx, before, later,
            Nat.add(Q.size(Con{Q.Configured{}, H.render_phase(m, phase)}), 0n), Q.Failed{stage, id, fatal}, canonical, trace,
            (%Equal.sym(List<&2, Q.Frame>, before, Con{Q.Configured{}, Closures.before_failure(m, phase, stage, id, fatal)}, prefix) :
              {Q.query(_, Nat.add(Q.size(Con{Q.Configured{}, H.render_phase(m, phase)}), 0n)) == Some{Q.Failed{stage, id, fatal}} : Maybe<&2, Q.Frame>}
              Adm.query_of_mark(Con{Q.Configured{}, H.render_phase(m, phase)}, Q.Failed{stage, id, fatal})), {==}, Unit{}))
    case H.InitialOk{}: match origin:
    case H.InitialRefusal{status}: match origin:
    case H.InitialFailure{accepts, stage, id, fatal}: match origin:
    case H.WithoutResponse{}: match origin:
    case H.Executed{req, ctx, xs, p, en}: match origin:
    case H.FatalAfterPublication{req, ctx, xs, p, stage, id}: match origin:
    case H.Pending{phase}: match origin:
    case H.InitialPending{accepts}: match origin:

def artifact_fixed_has_status_of_error(e: Errors.Error) -> Preparation.Error(Errors.status(e)):
  match e:
    case Errors.Input{}: Unit{}
    case Errors.Authentication{}: Unit{}
    case Errors.Certificate{}: Unit{}
    case Errors.DataError{}: Unit{}
    case Errors.Limit{}: Unit{}
    case Errors.Failure{}: Unit{}

def octets_of_state_copied(~c: S.Configuration, +s: D.State, +be: List<&2, U32>, state: Causes.StateCopied(c, s, be)) ->
  {B.octets_all_valid(be) == True{} : Bool}:
  match state:
    case (ce, te, L.Both{code, rest}): Octets.any_encoding_only_emits_octets(D.state_value(s), be, code)

def ContentFixed(~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception, +branch: H.Branch) -> Type:
  L.E<InputOfBranch(c, world, s, rx, branch), Source.RequestOfBranch(c, Source.Service{world, s, rx}, branch)>

def content_fixed_without_input(~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception,
  +be: List<&2, U32>, +data: H.DataTools, +branch: H.Branch,
  negative: {is_input(branch) == False{} : Bool}, selected: {branch == H.decide(c, rx, be, data) : H.Branch},
  state: Causes.StateCopied(c, s, be), octets_r: Two.OctetsReceived(X.decide_reception(c, rx))) -> ContentFixed(c, world, s, rx, branch):
  L.Both{without_input_has_cause(c, world, s, rx, branch, negative),
    (%Equal.sym(H.Branch, branch, H.decide(c, rx, be, data), selected) : Source.RequestOfBranch(c, Source.Service{world, s, rx}, _)
      Two.requests_of_decision(c, world, s, rx, be, data, octets_of_state_copied(c, s, be, state), octets_r))}

def content_fixed_of_decision(~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception,
  +be: List<&2, U32>, +data: H.DataTools, +branch: H.Branch,
  selected: {branch == H.decide(c, rx, be, data) : H.Branch},
  state: Causes.StateCopied(c, s, be), body: Causes.BodyCopied(c, rx),
  octets_r: Two.OctetsReceived(X.decide_reception(c, rx)), structure: {D.structure(S.schema(c), s) == True{} : Bool}) ->
  ContentFixed(c, world, s, rx, branch):
  match branch:
    case H.InputRefusal{+e, +closes, +en}:
      L.Both{(%Equal.sym(H.Branch, H.InputRefusal{e, closes, en}, H.decide(c, rx, be, data), selected) : InputOfBranch(c, world, s, rx, _)
        input_of_decision_has_cause_original(c, world, s, rx, be, data, state, body, octets_r, structure)), Unit{}}
    case H.AutRefusal{+req, +en}: content_fixed_without_input(c, world, s, rx, be, data, H.AutRefusal{req, en}, {==}, selected, state, octets_r)
    case H.GateRefusal{+req, +ctx, +en}: content_fixed_without_input(c, world, s, rx, be, data, H.GateRefusal{req, ctx, en}, {==}, selected, state, octets_r)
    case H.Executed{+req, +ctx, +xs, +p, +en}: content_fixed_without_input(c, world, s, rx, be, data, H.Executed{req, ctx, xs, p, en}, {==}, selected, state, octets_r)
    case H.FailureBefore{+phase, +stage, +id, +fatal, +en}: content_fixed_without_input(c, world, s, rx, be, data, H.FailureBefore{phase, stage, id, fatal, en}, {==}, selected, state, octets_r)
    case H.InitialOk{}: content_fixed_without_input(c, world, s, rx, be, data, H.InitialOk{}, {==}, selected, state, octets_r)
    case H.InitialRefusal{+status}: content_fixed_without_input(c, world, s, rx, be, data, H.InitialRefusal{status}, {==}, selected, state, octets_r)
    case H.InitialFailure{+accepts, +stage, +id, +fatal}: content_fixed_without_input(c, world, s, rx, be, data, H.InitialFailure{accepts, stage, id, fatal}, {==}, selected, state, octets_r)
    case H.WithoutResponse{}: content_fixed_without_input(c, world, s, rx, be, data, H.WithoutResponse{}, {==}, selected, state, octets_r)
    case H.FatalAfterPublication{+req, +ctx, +xs, +p, +stage, +id}: content_fixed_without_input(c, world, s, rx, be, data, H.FatalAfterPublication{req, ctx, xs, p, stage, id}, {==}, selected, state, octets_r)
    case H.Pending{+phase}: content_fixed_without_input(c, world, s, rx, be, data, H.Pending{phase}, {==}, selected, state, octets_r)
    case H.InitialPending{+accepts}: content_fixed_without_input(c, world, s, rx, be, data, H.InitialPending{accepts}, {==}, selected, state, octets_r)

def preparation_fixed_of_source(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception,
  +m: H.Micro, +before: List<&2, Q.Frame>, +later: List<&2, Q.Frame>, +e: Errors.Error, +branch: H.Branch,
  canonical: {I.Serve{world, c, s, rx} == Source.scenario(source, world) : I.Scenario},
  trace: {Vis.frames_call(c, s, rx, Source.call(source, world)) == Q.concatenate(before, Con{Closures.milestone_preparation(Closures.Fixed{e}), later}) : List<&2, Q.Frame>},
  is_valid: {R.configuration_is_valid(c) == True{} : Bool},
  origin: Closures.FixedOfBranch(e, branch), prefix: Closures.PrefixFixed(m, branch, before), content: ContentFixed(c, world, s, rx, branch)) ->
  K.Rule7(fact_preparation(Closures.milestone_preparation(Closures.Fixed{e})), Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, Nat.add(Q.size(before), 0n)):
  F.combined_pair(K.Rule7(fact_preparation(Closures.milestone_preparation(Closures.Fixed{e})), Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, Nat.add(Q.size(before), 0n)),
    InputOfBranch(c, world, s, rx, branch), Source.RequestOfBranch(c, Source.Service{world, s, rx}, branch), content,
    input => command => preparation_fixed_combined_cause_real_obeys_rule7(c, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, Nat.add(Q.size(before), 0n),
      Errors.status(e), Errors.bytes(e), {==}, is_valid, artifact_fixed_has_status_of_error(e), Errors.all_os_errors_prepared_are_exactly_messages_original(e),
      cause_fixed_of_branch(source, c, world, s, rx, m, before, Con{Closures.milestone_preparation(Closures.Fixed{e}), later}, e, branch, canonical, trace, origin, prefix, input, command)))

def mark_canonical_in_trace(+qs: List<&2, Q.Frame>, +before: List<&2, Q.Frame>, +later: List<&2, Q.Frame>,
  +r: S.Response, +bs: List<&2, U32>, +origin: Closures.OriginPreparation,
  trace: {qs == Q.concatenate(before, Con{Q.Prepared{r, bs}, later}) : List<&2, Q.Frame>},
  frame: {Q.Prepared{r, bs} == Closures.milestone_preparation(origin) : Q.Frame}) ->
  {qs == Q.concatenate(before, Con{Closures.milestone_preparation(origin), later}) : List<&2, Q.Frame>}:
  Equal.trans(List<&2, Q.Frame>, qs, Q.concatenate(before, Con{Q.Prepared{r, bs}, later}), Q.concatenate(before, Con{Closures.milestone_preparation(origin), later}), trace,
    Equal.cong(Q.Frame, List<&2, Q.Frame>, q => Q.concatenate(before, Con{q, later}), Q.Prepared{r, bs}, Closures.milestone_preparation(origin), frame))

def consume_origin_of_preparation(~source: Source.Source, ~c: S.Configuration, +world: Nat, +initial: D.State, +rx: X.Reception,
  +m: H.Micro, +code: Source.JudgmentSyntactic, +branch: H.Branch, +t: Nat, +r: S.Response, +bs: List<&2, U32>,
  canonical: {I.Serve{world, c, initial, rx} == Source.scenario(source, world) : I.Scenario},
  is_valid: {R.configuration_is_valid(c) == True{} : Bool},
  same_root: {Source.program(source, code) == Law5.program_of_world(source, world) : S.Program},
  content: ContentFixed(c, world, initial, rx, branch),
  preparation: Closures.PreparationInTrace(source, c, m, initial, code, branch, Vis.frames_call(c, initial, rx, Source.call(source, world)), t, r, bs)) ->
  K.Rule7(I.Prepared{r, bs}, Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, rx}, t):
  match preparation:
    case (+before, +later, Closures.Native{+req, +ctx, +xs, N.Prepared{+w, +ts, +rp, +bytes}}, L.Both{trace, L.Both{pos, L.Both{+frame, L.Both{prefix, real}}}}):
      transport_preparation7(Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, rx}, before, t, r, bs, Q.Prepared{rp, bytes}, pos, frame,
        preparation_native_of_source(source, c, world, initial, rx, m, before, later, req, ctx, code, xs, N.Prepared{w, ts, rp, bytes}, canonical,
          mark_canonical_in_trace(Vis.frames_call(c, initial, rx, Source.call(source, world)), before, later, r, bs, Closures.Native{req, ctx, xs, N.Prepared{w, ts, rp, bytes}}, trace, frame), prefix, real, is_valid, same_root))
    case (+before, +later, Closures.Fixed{+e}, L.Both{trace, L.Both{pos, L.Both{+frame, L.Both{origin, prefix}}}}):
      transport_preparation7(Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, rx}, before, t, r, bs, Closures.milestone_preparation(Closures.Fixed{e}), pos, frame,
        preparation_fixed_of_source(source, c, world, initial, rx, m, before, later, e, branch, canonical,
          mark_canonical_in_trace(Vis.frames_call(c, initial, rx, Source.call(source, world)), before, later, r, bs, Closures.Fixed{e}, trace, frame), is_valid, origin, prefix, content))

def StateOfCall(~c: S.Configuration, +s: D.State, data: Source.CallData) -> Type:
  match data:
    case Source.CallData{cf, pf, cert, terminates, be, tools, micro}: Causes.StateCopied(c, s, be)

def preparation_of_data_of_source(~source: Source.Source, ~c: S.Configuration, +world: Nat, +s: D.State, +rx: X.Reception,
  +data: Source.CallData, +t: Nat, +r: S.Response, +bs: List<&2, U32>,
  canonical: {I.Serve{world, c, s, rx} == Source.scenario(source, world) : I.Scenario},
  +same: {data == Source.call(source, world) : Source.CallData},
  real: Law5.CallReal(source, c, s, rx, data), state: StateOfCall(c, s, data), body: Causes.BodyCopied(c, rx),
  octets_r: Two.OctetsReceived(X.decide_reception(c, rx)), structure: {D.structure(S.schema(c), s) == True{} : Bool},
  is_valid: {R.configuration_is_valid(c) == True{} : Bool},
  observed: Source.of_observation(source, c, Source.construct_call(c, s, rx, data), t, I.Prepared{r, bs})) ->
  K.Rule7(I.Prepared{r, bs}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t):
  match data:
    case Source.CallData{+cf, +code, +cert, +terminates, +be, +tools, +micro}:
      consume_origin_of_preparation(source, c, world, s, rx, micro, code, H.decide(c, rx, be, tools), t, r, bs,
        canonical, is_valid, Law5.same_root_of_call(source, world, Source.CallData{cf, code, cert, terminates, be, tools, micro}, same),
        content_fixed_of_decision(c, world, s, rx, be, tools, H.decide(c, rx, be, tools), {==}, state, body, octets_r, structure),
        (%Equal.cong(Source.CallData, List<&2, Q.Frame>, d => Vis.frames_call(c, s, rx, d),
          Source.CallData{cf, code, cert, terminates, be, tools, micro}, Source.call(source, world), same) :
            Closures.PreparationInTrace(source, c, micro, s, code, H.decide(c, rx, be, tools), _, t, r, bs)
          Closures.invert_preparation(source, c, micro, s, code, H.decide(c, rx, be, tools), t, r, bs,
            Law5.execution_of_decision(source, c, s, code, be, tools, rx, real),
            Q.observation_frame(c, Source.program(source, code), H.generate(c, rx, be, s, tools, micro), t, I.Prepared{r, bs}, observed))))

law preparation_of_source_obeys_rule7:
  for ~source: Source.Source
  for ~c: S.Configuration
  for +world: Nat
  for +s: D.State
  for +rx: X.Reception
  for +t: Nat
  for +r: S.Response
  for +bs: List<&2, U32>
  for real: Law5.CallReal(source, c, s, rx, Source.call(source, world))
  for state: StateOfCall(c, s, Source.call(source, world))
  for body: Causes.BodyCopied(c, rx)
  for octets_r: Two.OctetsReceived(X.decide_reception(c, rx))
  for structure: {D.structure(S.schema(c), s) == True{} : Bool}
  for is_valid: {R.configuration_is_valid(c) == True{} : Bool}
  for observed: I.Happens(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t, I.Prepared{r, bs})
  K.Rule7(I.Prepared{r, bs}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t)
def preparation_of_source_obeys_rule7(source, c, world, s, rx, t, r, bs, real, state, body, octets_r, structure, is_valid, observed):
  F.combined_pair(K.Rule7(I.Prepared{r, bs}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t),
    {Source.artifact(source) == Source.artifact(source) : String},
    L.E<{I.Serve{world, c, s, rx} == Source.scenario(source, world) : I.Scenario}, Source.of_route(source, I.Serve{world, c, s, rx}, t, I.Prepared{r, bs})>,
    Source.eliminate_fact_literal(source, Source.artifact(source), I.Serve{world, c, s, rx}, t, I.Prepared{r, bs}, observed),
    name => origin => F.combined_pair(K.Rule7(I.Prepared{r, bs}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, rx}, t),
      {I.Serve{world, c, s, rx} == Source.scenario(source, world) : I.Scenario}, Source.of_route(source, I.Serve{world, c, s, rx}, t, I.Prepared{r, bs}), origin,
      canonical => obs => preparation_of_data_of_source(source, c, world, s, rx, Source.call(source, world), t, r, bs, canonical, {==}, real, state, body, octets_r, structure, is_valid, obs)))
