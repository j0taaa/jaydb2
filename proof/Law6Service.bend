# Publication of the same Bend result and visibility of the serial host.
import Base
import ./PublicationService.bend as PublicationService
import ./RefinementService.bend as Ref
import ../src/ConfigurationCheck.bend as Config
import ./LinkageService.bend as Linkage
import ./ClosuresService.bend as Closures
import ../contract/Data.bend as D
import ../contract/Interface.bend as I
import ../contract/LAWS.bend as K
import ../contract/Logic.bend as L
import ../contract/Resources.bend as X
import ../contract/Semantics.bend as S
import ../src/Core.bend as N
import ./SourceService.bend as Source
import ./RoutesService.bend as R
import ./ProtocolService.bend as Q
import ./VisibilityService.bend as Vis
import ./PhasesService.bend as Phases
import ./ConclusionService.bend as Conclusion
import ./Law5Service.bend as Five
import ./Publication.bend as U
import ./Foundations.bend as F
import ./Call.bend as Call
import ./ScenariosService.bend as Scenarios
import ./HistoryService.bend as History
import ./ModelService.bend as Model

# The next iteration inherits the previous conclusion; delivery does not repeat the store.
def OriginNext(-xs: List<&2, Q.Frame>, -t: Nat, -a: D.State, -b: D.State) -> Type:
  L.E<{b == a : D.State},
    &r: S.Response -> &closes: Bool -> &u: Nat ->
      L.E<{Nat.is_lt(u, t) == True{} : Bool},
        {Q.query(xs, u) == Some{Q.Completed{r, a, closes}} : Maybe<&2, Q.Frame>}>>

def first_next(q: Q.Frame) -> Maybe<&2, D.State>:
  match q:
    case Q.Next{a, b}: Some{a}
    case _: None{}

def second_next(q: Q.Frame) -> Maybe<&2, D.State>:
  match q:
    case Q.Next{a, b}: Some{b}
    case _: None{}

def states_of_succession(+s: D.State, +a: D.State, +b: D.State,
  equality: {Q.Next{s, s} == Q.Next{a, b} : Q.Frame}) ->
  L.E<{a == s : D.State}, {b == a : D.State}>:
  F.combined_pair(L.E<{a == s : D.State}, {b == a : D.State}>,
    {Q.Next{s, s} == Q.Next{a, b} : Q.Frame},
    {Q.Next{s, s} == Q.Next{a, b} : Q.Frame},
    Call.duplicate_equality(Q.Frame, Q.Next{s, s}, Q.Next{a, b}, equality),
    first => second =>
      F.combined_pair(L.E<{a == s : D.State}, {b == a : D.State}>,
        {a == s : D.State}, {a == s : D.State},
        Call.duplicate_equality(D.State, a, s,
          Equal.sym(D.State, s, a, F.some_injective(D.State, s, a,
            Equal.cong(Q.Frame, Maybe<&2, D.State>, first_next,
              Q.Next{s, s}, Q.Next{a, b}, first)))),
        initial => copy => L.Both{initial,
          Equal.trans(D.State, b, s, a,
            Equal.sym(D.State, s, b, F.some_injective(D.State, s, b,
              Equal.cong(Q.Frame, Maybe<&2, D.State>, second_next,
                Q.Next{s, s}, Q.Next{a, b}, second))),
            Equal.sym(D.State, a, s, copy))}))

def succession_local_present(+s: D.State, +r: S.Response, +bs: List<&2, U32>, t: Nat,
  +a: D.State, +b: D.State,
  present: {Q.query([Q.Completed{r, s, False{}}, Q.Delivered{bs}, Q.Next{s, s}], t) ==
    Some{Q.Next{a, b}} : Maybe<&2, Q.Frame>}) ->
  OriginNext([Q.Completed{r, s, False{}}, Q.Delivered{bs}, Q.Next{s, s}], t, a, b):
  match t:
    case 0n:
      L.ex_false(OriginNext([Q.Completed{r, s, False{}}, Q.Delivered{bs}, Q.Next{s, s}], 0n, a, b),
        Closures.without_next_in_front(Q.Completed{r, s, False{}}, Nil{}, a, b, {==}, Closures.without_next_empty(a, b))(0n, present))
    case 1n+k:
      match k:
        case 0n:
          L.ex_false(OriginNext([Q.Completed{r, s, False{}}, Q.Delivered{bs}, Q.Next{s, s}], 1n, a, b),
            Closures.without_next_in_front(Q.Delivered{bs}, Nil{}, a, b, {==}, Closures.without_next_empty(a, b))(0n, present))
        case 1n+j:
          match j:
            case 0n:
              F.combined_pair(OriginNext([Q.Completed{r, s, False{}}, Q.Delivered{bs}, Q.Next{s, s}], 2n, a, b),
                {a == s : D.State}, {b == a : D.State},
                states_of_succession(s, a, b, F.some_injective(Q.Frame, Q.Next{s, s}, Q.Next{a, b}, present)),
                same => preserves => L.Both{preserves, (r, False{}, 0n, L.Both{{==},
                  (%Equal.sym(D.State, a, s, same) :
                    {Some{Q.Completed{r, s, False{}}} == Some{Q.Completed{r, _, False{}}} : Maybe<&2, Q.Frame>} {==})})})
            case 1n+n:
              L.ex_false(OriginNext([Q.Completed{r, s, False{}}, Q.Delivered{bs}, Q.Next{s, s}], 3n+n, a, b),
                F.none_negative_some(Q.Frame, Q.Next{a, b}, present))

# Without another Next marker in the prefix, its origin remains unchanged when shifted.
def raise_origin_next(+before: List<&2, Q.Frame>, +rest: List<&2, Q.Frame>,
  -t: Nat, +i: Nat, -a: D.State, -b: D.State,
  position: {t == Nat.add(Q.size(before), i) : Nat},
  origin: OriginNext(rest, i, a, b)) ->
  OriginNext(Q.concatenate(before, rest), t, a, b):
  match origin:
    case L.Both{preserves, (r, closes, +u, L.Both{less, query_result})}:
      L.Both{preserves, (r, closes, Nat.add(Q.size(before), u), L.Both{
        (%Equal.sym(Nat, t, Nat.add(Q.size(before), i), position) :
          {Nat.is_lt(Nat.add(Q.size(before), u), _) == True{} : Bool}
          Q.order_shifted(Q.size(before), u, i, less)),
        Equal.trans(Maybe<&2, Q.Frame>,
          Q.query(Q.concatenate(before, rest), Nat.add(Q.size(before), u)),
          Q.query(rest, u), Some{Q.Completed{r, a, closes}},
          Q.query_after_prefix(before, rest, u), query_result)})}

# Only two N.conclude possibilities: success with prior store or rollback.
def end_negative_publish(-a: I.Environment, -k: String, -x: I.Scenario,
  +before: List<&2, Q.Frame>, +s: D.State, +r: S.Response, +bs: List<&2, U32>, +closes: Bool, +delivery: R.Delivery,
  without: {Phases.absent(Phases.Publication{}, before) == True{} : Bool},
  preserves: {U.status_success(r) == False{} : Bool} -> {s == I.initial(x) : D.State},
  status: {U.status_success(r) == False{} : Bool},
  extract: @u: Nat -> @w: D.State -> I.Happens(a, k, x, u, I.Published{w}) ->
    {Q.query(Q.concatenate(before, R.render_conclusion(N.Conclusion{s, r, bs}, closes, delivery)), u) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>}) ->
  L.E<{s == I.initial(x) : D.State}, K.NonePublication(a, k, x)>:
  F.combined_pair(L.E<{s == I.initial(x) : D.State}, K.NonePublication(a, k, x)>,
    {U.status_success(r) == False{} : Bool}, {U.status_success(r) == False{} : Bool},
    Call.duplicate_equality(Bool, U.status_success(r), False{}, status),
    previous => none => L.Both{preserves(previous),
      Phases.none_publication_real(a, k, x, Q.concatenate(before, R.render_conclusion(N.Conclusion{s, r, bs}, closes, delivery)),
        Phases.concatenate_absence(Phases.Publication{}, before, R.render_conclusion(N.Conclusion{s, r, bs}, closes, delivery),
          without, Phases.response_negative_publish(s, r, bs, closes, delivery, none)), extract)})

def atomic_of_closure(-a: I.Environment, -k: String, -x: I.Scenario,
  +before: List<&2, Q.Frame>, +s: D.State, r: S.Response, +bs: List<&2, U32>, +closes: Bool, +delivery: R.Delivery,
  without: {Phases.absent(Phases.Publication{}, before) == True{} : Bool},
  preserves: {U.status_success(r) == False{} : Bool} -> {s == I.initial(x) : D.State},
  introduce: @u: Nat -> @w: D.State ->
    {Q.query(Q.concatenate(before, R.render_conclusion(N.Conclusion{s, r, bs}, closes, delivery)), u) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>} ->
    I.Happens(a, k, x, u, I.Published{w}),
  extract: @u: Nat -> @w: D.State -> I.Happens(a, k, x, u, I.Published{w}) ->
    {Q.query(Q.concatenate(before, R.render_conclusion(N.Conclusion{s, r, bs}, closes, delivery)), u) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>}) ->
  K.ConclusionAtomic(r, a, k, x, Nat.add(Q.size(before), Conclusion.local_conclusion(s, r, bs)), s):
  match r:
    case S.Response{S.Success{}, +v}:
      (Nat.add(Q.size(before), 1n), L.Both{Q.order_shifted(Q.size(before), 1n, 2n, {==}),
        introduce(Nat.add(Q.size(before), 1n), s,
          Q.query_after_prefix(before, R.render_conclusion(N.Conclusion{s, S.Response{S.Success{}, v}, bs}, closes, delivery), 1n))})
    case S.Response{S.Refusal{}, v}: end_negative_publish(a, k, x, before, s, S.Response{S.Refusal{}, v}, bs, closes, delivery, without, preserves, {==}, extract)
    case S.Response{S.Input{}, v}: end_negative_publish(a, k, x, before, s, S.Response{S.Input{}, v}, bs, closes, delivery, without, preserves, {==}, extract)
    case S.Response{S.Authentication{}, v}: end_negative_publish(a, k, x, before, s, S.Response{S.Authentication{}, v}, bs, closes, delivery, without, preserves, {==}, extract)
    case S.Response{S.Certificate{}, v}: end_negative_publish(a, k, x, before, s, S.Response{S.Certificate{}, v}, bs, closes, delivery, without, preserves, {==}, extract)
    case S.Response{S.DataError{}, v}: end_negative_publish(a, k, x, before, s, S.Response{S.DataError{}, v}, bs, closes, delivery, without, preserves, {==}, extract)
    case S.Response{S.Limit{}, v}: end_negative_publish(a, k, x, before, s, S.Response{S.Limit{}, v}, bs, closes, delivery, without, preserves, {==}, extract)
    case S.Response{S.Failure{}, v}: end_negative_publish(a, k, x, before, s, S.Response{S.Failure{}, v}, bs, closes, delivery, without, preserves, {==}, extract)

def transport_conclusion6(-a: I.Environment, -k: String, -x: I.Scenario,
  +before: List<&2, Q.Frame>, +s: D.State, +r: S.Response, +bs: List<&2, U32>, +closure: Bool,
  -t: Nat, +q: Q.Frame,
  equal: L.E<{t == Nat.add(Q.size(before), Conclusion.local_conclusion(s, r, bs)) : Nat},
    {q == Q.Completed{r, s, closure} : Q.Frame}>,
  atomic: K.ConclusionAtomic(r, a, k, x, Nat.add(Q.size(before), Conclusion.local_conclusion(s, r, bs)), s)) ->
  K.Rule6(Conclusion.fact_of_conclusion(q), a, k, x, t):
  match equal:
    case L.Both{pos, fields}:
      %Equal.sym(Nat, t, Nat.add(Q.size(before), Conclusion.local_conclusion(s, r, bs)), pos) :
        K.Rule6(Conclusion.fact_of_conclusion(q), a, k, x, _)
      %Equal.sym(Q.Frame, q, Q.Completed{r, s, closure}, fields) :
        K.Rule6(Conclusion.fact_of_conclusion(_), a, k, x, Nat.add(Q.size(before), Conclusion.local_conclusion(s, r, bs)))
      atomic

law conclusion_of_closure_obeys_rule6:
  for -a: I.Environment
  for -k: String
  for -x: I.Scenario
  for +before: List<&2, Q.Frame>
  for +s: D.State
  for +r: S.Response
  for +bs: List<&2, U32>
  for +closure: Bool
  for +delivery: R.Delivery
  for +t: Nat
  for +r2: S.Response
  for +s2: D.State
  for +f2: Bool
  for without_publish: {Phases.absent(Phases.Publication{}, before) == True{} : Bool}
  for without_conclude: {Phases.absent(Phases.Conclusion{}, before) == True{} : Bool}
  for preserves: {U.status_success(r) == False{} : Bool} -> {s == I.initial(x) : D.State}
  for query_result: {Q.query(Q.concatenate(before, R.render_conclusion(N.Conclusion{s, r, bs}, closure, delivery)), t) == Some{Q.Completed{r2, s2, f2}} : Maybe<&2, Q.Frame>}
  for introduce: @u: Nat -> @w: D.State ->
    {Q.query(Q.concatenate(before, R.render_conclusion(N.Conclusion{s, r, bs}, closure, delivery)), u) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>} ->
    I.Happens(a, k, x, u, I.Published{w})
  for extract: @u: Nat -> @w: D.State -> I.Happens(a, k, x, u, I.Published{w}) ->
    {Q.query(Q.concatenate(before, R.render_conclusion(N.Conclusion{s, r, bs}, closure, delivery)), u) == Some{Q.Published{w}} : Maybe<&2, Q.Frame>}
  K.Rule6(I.Concluded{r2, s2, f2}, a, k, x, t)
def conclusion_of_closure_obeys_rule6(a, k, x, before, s, r, bs, closure, delivery, t, r2, s2, f2,
  without_publish, without_conclude, preserves, query_result, introduce, extract):
  transport_conclusion6(a, k, x, before, s, r, bs, closure, t, Q.Completed{r2, s2, f2},
    Conclusion.conclusion_located_in_closure(before, s, r, bs, closure, delivery, t, Q.Completed{r2, s2, f2}, without_conclude, {==}, query_result),
    atomic_of_closure(a, k, x, before, s, r, bs, closure, delivery, without_publish, preserves, introduce, extract))

# Three uses of equality reorder the SAME list, without a new observer.
def conclusion_according_closure(~source: Source.Source, ~c: S.Configuration,
  +world: Nat, +initial: D.State, +reception: X.Reception,
  +before: List<&2, Q.Frame>, +s: D.State, +r: S.Response, +bs: List<&2, U32>, +closure: Bool, +delivery: R.Delivery,
  +t: Nat, +r2: S.Response, +s2: D.State, +f2: Bool,
  canonical: {I.Serve{world, c, initial, reception} == Source.scenario(source, world) : I.Scenario},
  same: {Vis.frames_call(c, initial, reception, Source.call(source, world)) ==
    Q.concatenate(before, R.render_conclusion(N.Conclusion{s, r, bs}, closure, delivery)) : List<&2, Q.Frame>},
  pub: {Phases.absent(Phases.Publication{}, before) == True{} : Bool},
  concl: {Phases.absent(Phases.Conclusion{}, before) == True{} : Bool},
  preserves: {U.status_success(r) == False{} : Bool} -> {s == initial : D.State},
  query_result: {Q.query(Vis.frames_call(c, initial, reception, Source.call(source, world)), t) ==
    Some{Q.Completed{r2, s2, f2}} : Maybe<&2, Q.Frame>}) ->
  K.Rule6(I.Concluded{r2, s2, f2}, Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, reception}, t):
  Five.combined_four(
    {Vis.frames_call(c, initial, reception, Source.call(source, world)) ==
      Q.concatenate(before, R.render_conclusion(N.Conclusion{s, r, bs}, closure, delivery)) : List<&2, Q.Frame>},
    K.Rule6(I.Concluded{r2, s2, f2}, Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, reception}, t),
    Five.four_equalities(List<&2, Q.Frame>, Vis.frames_call(c, initial, reception, Source.call(source, world)),
      Q.concatenate(before, R.render_conclusion(N.Conclusion{s, r, bs}, closure, delivery)), same),
    current => introduce => extract => remainder =>
      conclusion_of_closure_obeys_rule6(Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, reception},
        before, s, r, bs, closure, delivery, t, r2, s2, f2, pub, concl, preserves,
        (%current : {Q.query(_, t) == Some{Q.Completed{r2, s2, f2}} : Maybe<&2, Q.Frame>} query_result),
        +u => +w => present => Linkage.introduce_in_list(source, c, world, initial, reception,
          Q.concatenate(before, R.render_conclusion(N.Conclusion{s, r, bs}, closure, delivery)), u, Q.Published{w}, I.Published{w},
          canonical, introduce, present, {==}, Unit{}),
        +u => +w => fact => Linkage.extract_in_list(source, c, world, initial, reception,
          Q.concatenate(before, R.render_conclusion(N.Conclusion{s, r, bs}, closure, delivery)), u, I.Published{w}, extract, Unit{}, fact)))

def consume_closure_of_call(~source: Source.Source, ~c: S.Configuration,
  +world: Nat, +initial: D.State, +reception: X.Reception, +xs: List<&2, Q.Frame>, +branch: R.Branch,
  +t: Nat, +r: S.Response, +s: D.State, +closes: Bool,
  canonical: {I.Serve{world, c, initial, reception} == Source.scenario(source, world) : I.Scenario},
  same: {Vis.frames_call(c, initial, reception, Source.call(source, world)) == xs : List<&2, Q.Frame>},
  query_result: {Q.query(Vis.frames_call(c, initial, reception, Source.call(source, world)), t) == Some{Q.Completed{r, s, closes}} : Maybe<&2, Q.Frame>},
  result: &h: Closures.Closure -> L.E<Closures.Form(xs, branch, Some{h}), Closures.StateOfClosure(initial, Some{h})>) ->
  K.Rule6(I.Concluded{r, s, closes}, Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, reception}, t):
  match result:
    case (Closures.Closure{before, N.Conclusion{w, rp, bs}, closure, delivery, origin},
      L.Both{L.Both{same_branch, L.Both{trace, L.Both{pub, concl}}}, state}):
      conclusion_according_closure(source, c, world, initial, reception, before, w, rp, bs, closure, delivery, t, r, s, closes,
        canonical, Equal.trans(List<&2, Q.Frame>, Vis.frames_call(c, initial, reception, Source.call(source, world)), xs,
          Q.concatenate(before, R.render_conclusion(N.Conclusion{w, rp, bs}, closure, delivery)), same, trace), pub, concl, state, query_result)

def conclusion_by_guards(~source: Source.Source, ~c: S.Configuration,
  +world: Nat, +s: D.State, +reception: X.Reception, +t: Nat, +r: S.Response, +w: D.State, +closes: Bool,
  input: L.E<{Source.artifact(source) == Source.artifact(source) : String},
    L.E<{I.Serve{world, c, s, reception} == Source.scenario(source, world) : I.Scenario},
      Source.of_route(source, I.Serve{world, c, s, reception}, t, I.Concluded{r, w, closes})>>) ->
  K.Rule6(I.Concluded{r, w, closes}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t):
  match input:
    case L.Both{name, L.Both{canonical, observed}}:
      F.combined_pair(K.Rule6(I.Concluded{r, w, closes}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t),
        {Q.query(Vis.frames_call(c, s, reception, Source.call(source, world)), t) == Some{Q.Completed{r, w, closes}} : Maybe<&2, Q.Frame>},
        {Q.query(Vis.frames_call(c, s, reception, Source.call(source, world)), t) == Some{Q.Completed{r, w, closes}} : Maybe<&2, Q.Frame>},
        Call.duplicate_equality(Maybe<&2, Q.Frame>, Q.query(Vis.frames_call(c, s, reception, Source.call(source, world)), t), Some{Q.Completed{r, w, closes}},
          Linkage.frame_of_observation(source, c, s, reception, Source.call(source, world), t, I.Concluded{r, w, closes}, Unit{}, observed)),
        search => query_result => consume_closure_of_call(source, c, world, s, reception,
          R.render(Linkage.micro_of_data(Source.call(source, world)), s, Linkage.branch_of_data(c, reception, Source.call(source, world))),
          Linkage.branch_of_data(c, reception, Source.call(source, world)), t, r, w, closes, canonical,
          Linkage.frames_follow_o_branch(c, s, reception, Source.call(source, world)), query_result,
          Closures.invert_conclusion_combined_state(Linkage.micro_of_data(Source.call(source, world)), s,
            Linkage.branch_of_data(c, reception, Source.call(source, world)), t, r, w, closes,
            (%Linkage.frames_follow_o_branch(c, s, reception, Source.call(source, world)) :
              {Q.query(_, t) == Some{Q.Completed{r, w, closes}} : Maybe<&2, Q.Frame>} search))))

law conclusion_of_source_obeys_rule6:
  for ~source: Source.Source
  for ~c: S.Configuration
  for +world: Nat
  for +s: D.State
  for +reception: X.Reception
  for +t: Nat
  for +r: S.Response
  for +w: D.State
  for +closes: Bool
  for observed: I.Happens(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t, I.Concluded{r, w, closes})
  K.Rule6(I.Concluded{r, w, closes}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t)
def conclusion_of_source_obeys_rule6(source, c, world, s, reception, t, r, w, closes, observed):
  conclusion_by_guards(source, c, world, s, reception, t, r, w, closes,
    Source.eliminate_fact_literal(source, Source.artifact(source), I.Serve{world, c, s, reception}, t, I.Concluded{r, w, closes}, observed))

def negate_next(-xs: List<&2, Q.Frame>, +t: Nat, +a: D.State, +b: D.State,
  without: Closures.WithoutNext(xs), query_result: {Q.query(xs, t) == Some{Q.Next{a, b}} : Maybe<&2, Q.Frame>}) -> OriginNext(xs, t, a, b):
  L.ex_false(OriginNext(xs, t, a, b), without(a, b, t, query_result))

def succession_complete(+s: D.State, +r: S.Response, +bs: List<&2, U32>, +closes: Bool,
  +next: Bool, +t: Nat, +a: D.State, +b: D.State,
  query_result: {Q.query(Con{Q.Completed{r, s, closes}, R.render_delivery(s, bs, closes, R.Complete{next})}, t) == Some{Q.Next{a, b}} : Maybe<&2, Q.Frame>}) ->
  OriginNext(Con{Q.Completed{r, s, closes}, R.render_delivery(s, bs, closes, R.Complete{next})}, t, a, b):
  match closes:
    case True{}:
      negate_next([Q.Completed{r, s, True{}}, Q.Delivered{bs}, Q.Closed{}], t, a, b,
        Closures.prefix_without_next(Q.Completed{r, s, True{}}, [Q.Delivered{bs}, Q.Closed{}], {==},
          Closures.prefix_without_next(Q.Delivered{bs}, [Q.Closed{}], {==},
            Closures.prefix_without_next(Q.Closed{}, Nil{}, {==}, Closures.empty_without_next()))), query_result)
    case False{}:
      match next:
        case False{}:
          negate_next([Q.Completed{r, s, False{}}, Q.Delivered{bs}], t, a, b,
            Closures.prefix_without_next(Q.Completed{r, s, False{}}, [Q.Delivered{bs}], {==},
              Closures.prefix_without_next(Q.Delivered{bs}, Nil{}, {==}, Closures.empty_without_next())), query_result)
        case True{}: succession_local_present(s, r, bs, t, a, b, query_result)

def succession_later_of_conclusion(+s: D.State, +r: S.Response, +bs: List<&2, U32>, +closes: Bool,
  delivery: R.Delivery, +t: Nat, +a: D.State, +b: D.State,
  query_result: {Q.query(Con{Q.Completed{r, s, closes}, R.render_delivery(s, bs, closes, delivery)}, t) == Some{Q.Next{a, b}} : Maybe<&2, Q.Frame>}) ->
  OriginNext(Con{Q.Completed{r, s, closes}, R.render_delivery(s, bs, closes, delivery)}, t, a, b):
  match delivery:
    case R.PendingDelivery{}:
      negate_next([Q.Completed{r, s, closes}], t, a, b,
        Closures.prefix_without_next(Q.Completed{r, s, closes}, Nil{}, {==}, Closures.empty_without_next()), query_result)
    case R.Broken{+prefix}:
      negate_next([Q.Completed{r, s, closes}, Q.Interrupted{prefix}, Q.Closed{}], t, a, b,
        Closures.prefix_without_next(Q.Completed{r, s, closes}, [Q.Interrupted{prefix}, Q.Closed{}], {==},
          Closures.prefix_without_next(Q.Interrupted{prefix}, [Q.Closed{}], {==},
            Closures.prefix_without_next(Q.Closed{}, Nil{}, {==}, Closures.empty_without_next()))), query_result)
    case R.Complete{next}: succession_complete(s, r, bs, closes, next, t, a, b, query_result)

def part_previous_of_conclusion(+before: List<&2, Q.Frame>, +s: D.State, +r: S.Response, +bs: List<&2, U32>) -> List<&2, Q.Frame>:
  Q.concatenate(before, Con{Q.Prepared{r, bs}, R.render_publication(r, s)})

def separate_conclusion(+before: List<&2, Q.Frame>, +s: D.State, +r: S.Response, +bs: List<&2, U32>, +closes: Bool, +delivery: R.Delivery) ->
  {Q.concatenate(before, R.render_conclusion(N.Conclusion{s, r, bs}, closes, delivery)) ==
    Q.concatenate(part_previous_of_conclusion(before, s, r, bs), Con{Q.Completed{r, s, closes}, R.render_delivery(s, bs, closes, delivery)}) : List<&2, Q.Frame>}:
  Equal.sym(List<&2, Q.Frame>,
    Q.concatenate(part_previous_of_conclusion(before, s, r, bs), Con{Q.Completed{r, s, closes}, R.render_delivery(s, bs, closes, delivery)}),
    Q.concatenate(before, R.render_conclusion(N.Conclusion{s, r, bs}, closes, delivery)),
    Q.concatenate_assoc(before, Con{Q.Prepared{r, bs}, R.render_publication(r, s)},
      Con{Q.Completed{r, s, closes}, R.render_delivery(s, bs, closes, delivery)}))

def succession_of_part(+before: List<&2, Q.Frame>, +s: D.State, +r: S.Response, +bs: List<&2, U32>, +closes: Bool, +delivery: R.Delivery,
  +t: Nat, +a: D.State, +b: D.State,
  found: &i: Nat -> L.E<{t == Nat.add(Q.size(part_previous_of_conclusion(before, s, r, bs)), i) : Nat},
    {Q.query(Con{Q.Completed{r, s, closes}, R.render_delivery(s, bs, closes, delivery)}, i) == Some{Q.Next{a, b}} : Maybe<&2, Q.Frame>}>) ->
  OriginNext(Q.concatenate(part_previous_of_conclusion(before, s, r, bs),
    Con{Q.Completed{r, s, closes}, R.render_delivery(s, bs, closes, delivery)}), t, a, b):
  match found:
    case (+i, L.Both{index, query_result}):
      raise_origin_next(part_previous_of_conclusion(before, s, r, bs),
        Con{Q.Completed{r, s, closes}, R.render_delivery(s, bs, closes, delivery)}, t, i, a, b, index,
        succession_later_of_conclusion(s, r, bs, closes, delivery, i, a, b, query_result))

law succession_in_closure:
  for +before: List<&2, Q.Frame>
  for +s: D.State
  for +r: S.Response
  for +bs: List<&2, U32>
  for +closes: Bool
  for +delivery: R.Delivery
  for +t: Nat
  for +a: D.State
  for +b: D.State
  for without: Closures.WithoutNext(before)
  for query_result: {Q.query(Q.concatenate(before, R.render_conclusion(N.Conclusion{s, r, bs}, closes, delivery)), t) == Some{Q.Next{a, b}} : Maybe<&2, Q.Frame>}
  OriginNext(Q.concatenate(before, R.render_conclusion(N.Conclusion{s, r, bs}, closes, delivery)), t, a, b)
def succession_in_closure(before, s, r, bs, closes, delivery, t, a, b, without, query_result):
  %Equal.sym(List<&2, Q.Frame>, Q.concatenate(before, R.render_conclusion(N.Conclusion{s, r, bs}, closes, delivery)),
    Q.concatenate(part_previous_of_conclusion(before, s, r, bs), Con{Q.Completed{r, s, closes}, R.render_delivery(s, bs, closes, delivery)}),
    separate_conclusion(before, s, r, bs, closes, delivery)) : OriginNext(_, t, a, b)
  succession_of_part(before, s, r, bs, closes, delivery, t, a, b,
    Five.remove_prefix_without_frame(part_previous_of_conclusion(before, s, r, bs),
      Con{Q.Completed{r, s, closes}, R.render_delivery(s, bs, closes, delivery)}, t, Q.Next{a, b},
      Closures.concatenate_without_next(before, Con{Q.Prepared{r, bs}, R.render_publication(r, s)}, without,
        Closures.prefix_without_next(Q.Prepared{r, bs}, R.render_publication(r, s), {==}, Closures.publication_without_next(r, s)))(a, b),
      (%separate_conclusion(before, s, r, bs, closes, delivery) : {Q.query(_, t) == Some{Q.Next{a, b}} : Maybe<&2, Q.Frame>} query_result)))

def origin_next_becomes_rule6(-a: I.Environment, -k: String, -x: I.Scenario,
  +xs: List<&2, Q.Frame>, -t: Nat, +previous: D.State, -next: D.State,
  origin: OriginNext(xs, t, previous, next),
  record: @u: Nat -> @r: S.Response -> @closes: Bool ->
    {Q.query(xs, u) == Some{Q.Completed{r, previous, closes}} : Maybe<&2, Q.Frame>} ->
    I.Happens(a, k, x, u, I.Concluded{r, previous, closes})) ->
  K.Rule6(I.NextCall{previous, next}, a, k, x, t):
  match origin:
    case L.Both{equal, (+r, +closes, +u, L.Both{order, query_result})}:
      L.Both{equal, (r, closes, u, L.Both{order, record(u, r, closes, query_result)})}

def succession_according_closure(~source: Source.Source, ~c: S.Configuration,
  +world: Nat, +initial: D.State, +reception: X.Reception, +before: List<&2, Q.Frame>, +s: D.State,
  +r: S.Response, +bs: List<&2, U32>, +closes: Bool, +delivery: R.Delivery, +t: Nat, +a: D.State, +b: D.State,
  canonical: {I.Serve{world, c, initial, reception} == Source.scenario(source, world) : I.Scenario},
  same: {Vis.frames_call(c, initial, reception, Source.call(source, world)) ==
    Q.concatenate(before, R.render_conclusion(N.Conclusion{s, r, bs}, closes, delivery)) : List<&2, Q.Frame>},
  without: Closures.WithoutNext(before),
  query_result: {Q.query(Vis.frames_call(c, initial, reception, Source.call(source, world)), t) == Some{Q.Next{a, b}} : Maybe<&2, Q.Frame>}) ->
  K.Rule6(I.NextCall{a, b}, Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, reception}, t):
  F.combined_pair(K.Rule6(I.NextCall{a, b}, Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, reception}, t),
    {Vis.frames_call(c, initial, reception, Source.call(source, world)) == Q.concatenate(before, R.render_conclusion(N.Conclusion{s, r, bs}, closes, delivery)) : List<&2, Q.Frame>},
    {Vis.frames_call(c, initial, reception, Source.call(source, world)) == Q.concatenate(before, R.render_conclusion(N.Conclusion{s, r, bs}, closes, delivery)) : List<&2, Q.Frame>},
    Call.duplicate_equality(List<&2, Q.Frame>, Vis.frames_call(c, initial, reception, Source.call(source, world)),
      Q.concatenate(before, R.render_conclusion(N.Conclusion{s, r, bs}, closes, delivery)), same),
    observed => introduce =>
      origin_next_becomes_rule6(Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, reception},
        Q.concatenate(before, R.render_conclusion(N.Conclusion{s, r, bs}, closes, delivery)), t, a, b,
        succession_in_closure(before, s, r, bs, closes, delivery, t, a, b, without,
          (%observed : {Q.query(_, t) == Some{Q.Next{a, b}} : Maybe<&2, Q.Frame>} query_result)),
        +u => +rp => +f => present => Linkage.introduce_in_list(source, c, world, initial, reception,
          Q.concatenate(before, R.render_conclusion(N.Conclusion{s, r, bs}, closes, delivery)), u,
          Q.Completed{rp, a, f}, I.Concluded{rp, a, f}, canonical, introduce, present, {==}, Unit{})))

def consume_closure_next(~source: Source.Source, ~c: S.Configuration,
  +world: Nat, +initial: D.State, +reception: X.Reception, +xs: List<&2, Q.Frame>, +branch: R.Branch,
  +t: Nat, +a: D.State, +b: D.State,
  canonical: {I.Serve{world, c, initial, reception} == Source.scenario(source, world) : I.Scenario},
  same: {Vis.frames_call(c, initial, reception, Source.call(source, world)) == xs : List<&2, Q.Frame>},
  query_result: {Q.query(Vis.frames_call(c, initial, reception, Source.call(source, world)), t) == Some{Q.Next{a, b}} : Maybe<&2, Q.Frame>},
  result: &h: Closures.Closure -> L.E<Closures.Form(xs, branch, Some{h}), Closures.BeforeWithoutNext(Some{h})>) ->
  K.Rule6(I.NextCall{a, b}, Source.environment(source), Source.artifact(source), I.Serve{world, c, initial, reception}, t):
  match result:
    case (Closures.Closure{before, N.Conclusion{s, r, bs}, closes, delivery, origin},
      L.Both{L.Both{same_branch, L.Both{trace, L.Both{pub, concl}}}, without}):
      succession_according_closure(source, c, world, initial, reception, before, s, r, bs, closes, delivery, t, a, b, canonical,
        Equal.trans(List<&2, Q.Frame>, Vis.frames_call(c, initial, reception, Source.call(source, world)), xs,
          Q.concatenate(before, R.render_conclusion(N.Conclusion{s, r, bs}, closes, delivery)), same, trace), without, query_result)

def succession_by_guards(~source: Source.Source, ~c: S.Configuration,
  +world: Nat, +s: D.State, +reception: X.Reception, +t: Nat, +a: D.State, +b: D.State,
  input: L.E<{Source.artifact(source) == Source.artifact(source) : String},
    L.E<{I.Serve{world, c, s, reception} == Source.scenario(source, world) : I.Scenario},
      Source.of_route(source, I.Serve{world, c, s, reception}, t, I.NextCall{a, b})>>) ->
  K.Rule6(I.NextCall{a, b}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t):
  match input:
    case L.Both{name, L.Both{canonical, observed}}:
      F.combined_pair(K.Rule6(I.NextCall{a, b}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t),
        {Q.query(Vis.frames_call(c, s, reception, Source.call(source, world)), t) == Some{Q.Next{a, b}} : Maybe<&2, Q.Frame>},
        {Q.query(Vis.frames_call(c, s, reception, Source.call(source, world)), t) == Some{Q.Next{a, b}} : Maybe<&2, Q.Frame>},
        Call.duplicate_equality(Maybe<&2, Q.Frame>, Q.query(Vis.frames_call(c, s, reception, Source.call(source, world)), t), Some{Q.Next{a, b}},
          Linkage.frame_of_observation(source, c, s, reception, Source.call(source, world), t, I.NextCall{a, b}, Unit{}, observed)),
        search => query_result => consume_closure_next(source, c, world, s, reception,
          R.render(Linkage.micro_of_data(Source.call(source, world)), s, Linkage.branch_of_data(c, reception, Source.call(source, world))),
          Linkage.branch_of_data(c, reception, Source.call(source, world)), t, a, b, canonical,
          Linkage.frames_follow_o_branch(c, s, reception, Source.call(source, world)), query_result,
          Closures.invert_next(Linkage.micro_of_data(Source.call(source, world)), s,
            Linkage.branch_of_data(c, reception, Source.call(source, world)), t, a, b,
            (%Linkage.frames_follow_o_branch(c, s, reception, Source.call(source, world)) :
              {Q.query(_, t) == Some{Q.Next{a, b}} : Maybe<&2, Q.Frame>} search))))

law succession_of_source_obeys_rule6:
  for ~source: Source.Source
  for ~c: S.Configuration
  for +world: Nat
  for +s: D.State
  for +reception: X.Reception
  for +t: Nat
  for +a: D.State
  for +b: D.State
  for observed: I.Happens(Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t, I.NextCall{a, b})
  K.Rule6(I.NextCall{a, b}, Source.environment(source), Source.artifact(source), I.Serve{world, c, s, reception}, t)
def succession_of_source_obeys_rule6(source, c, world, s, reception, t, a, b, observed):
  succession_by_guards(source, c, world, s, reception, t, a, b,
    Source.eliminate_fact_literal(source, Source.artifact(source), I.Serve{world, c, s, reception}, t, I.NextCall{a, b}, observed))


def initial_negative_concludes_data(~source: Source.Source, ~c: S.Configuration, +s: D.State,
  +data: Source.InitialData, +t: Nat, +r: S.Response, +w: D.State, +closes: Bool,
  obs: Source.of_observation(source, c, Source.construct_initial(Source.identity(source), c, s, data), t, I.Concluded{r, w, closes})) -> Empty:
  match data:
    case Source.InitialData{cf, sf, pf, +j, +result, +micro}:
      Phases.absent_excludes_query(Phases.Conclusion{}, R.generate_result_initial(c, Source.identity(source), s, j, result, micro),
        t, Q.Completed{r, w, closes},
        L.and_left({Phases.absent(Phases.Conclusion{}, R.generate_result_initial(c, Source.identity(source), s, j, result, micro)) == True{} : Bool},
          Closures.WithoutNext(R.generate_result_initial(c, Source.identity(source), s, j, result, micro)),
          Closures.exclusions_of_start(micro, s, j, result, Config.is_valid(c, Source.identity(source)))), {==},
        Q.observation_frame(c, Source.without_program(), R.generate_result_initial(c, Source.identity(source), s, j, result, micro), t, I.Concluded{r, w, closes}, obs))

def initial_negative_succeeds_data(~source: Source.Source, ~c: S.Configuration, +s: D.State,
  +data: Source.InitialData, +t: Nat, +a: D.State, +b: D.State,
  obs: Source.of_observation(source, c, Source.construct_initial(Source.identity(source), c, s, data), t, I.NextCall{a, b})) -> Empty:
  match data:
    case Source.InitialData{cf, sf, pf, +j, +result, +micro}:
      L.and_right({Phases.absent(Phases.Conclusion{}, R.generate_result_initial(c, Source.identity(source), s, j, result, micro)) == True{} : Bool},
        Closures.WithoutNext(R.generate_result_initial(c, Source.identity(source), s, j, result, micro)),
        Closures.exclusions_of_start(micro, s, j, result, Config.is_valid(c, Source.identity(source))))(a, b, t,
          Q.observation_frame(c, Source.without_program(), R.generate_result_initial(c, Source.identity(source), s, j, result, micro), t, I.NextCall{a, b}, obs))

def conclusion_initial_and_impossible(~source: Source.Source, ~c: S.Configuration,
  +world: Nat, +s: D.State, +pi: String, +t: Nat, +r: S.Response, +w: D.State, +closes: Bool,
  obs: I.Happens(Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t, I.Concluded{r, w, closes})) -> Empty:
  initial_negative_concludes_data(source, c, s, Source.initial(source, world), t, r, w, closes,
    Ref.remove_guards({Source.artifact(source) == Source.artifact(source) : String},
      {I.Initialize{world, c, s, pi} == Source.scenario(source, world) : I.Scenario},
      Source.of_route(source, I.Initialize{world, c, s, pi}, t, I.Concluded{r, w, closes}),
      Source.eliminate_fact_literal(source, Source.artifact(source), I.Initialize{world, c, s, pi}, t, I.Concluded{r, w, closes}, obs)))

def succession_initial_and_impossible(~source: Source.Source, ~c: S.Configuration,
  +world: Nat, +s: D.State, +pi: String, +t: Nat, +a: D.State, +b: D.State,
  obs: I.Happens(Source.environment(source), Source.artifact(source), I.Initialize{world, c, s, pi}, t, I.NextCall{a, b})) -> Empty:
  initial_negative_succeeds_data(source, c, s, Source.initial(source, world), t, a, b,
    Ref.remove_guards({Source.artifact(source) == Source.artifact(source) : String},
      {I.Initialize{world, c, s, pi} == Source.scenario(source, world) : I.Scenario},
      Source.of_route(source, I.Initialize{world, c, s, pi}, t, I.NextCall{a, b}),
      Source.eliminate_fact_literal(source, Source.artifact(source), I.Initialize{world, c, s, pi}, t, I.NextCall{a, b}, obs)))

def rule6_initial(~source: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~pi: String, +world: Nat, +t: Nat, f: I.Fact,
  origin: PublicationService.OriginOfMoment(source, c, seed, history, world, Scenarios.Initialization{}),
  obs: I.Happens(Source.environment(source), Source.artifact(source), I.Initialize{world, c, seed(Unit{}), pi}, t, f)) ->
  K.Rule6(f, Source.environment(source), Source.artifact(source), I.Initialize{world, c, seed(Unit{}), pi}, t):
  match f:
    case I.Published{w}: PublicationService.publication_by_moment(source, c, seed, history, pi, world, Scenarios.Initialization{}, t, w, origin, obs)
    case I.StateVisible{w}: Vis.visibility_initial_source_obeys_rule6(source, c, world, seed(Unit{}), pi, t, w, obs)
    case I.Concluded{r, w, closes}:
      L.ex_false(K.Rule6(I.Concluded{r, w, closes}, Source.environment(source), Source.artifact(source), I.Initialize{world, c, seed(Unit{}), pi}, t),
        conclusion_initial_and_impossible(source, c, world, seed(Unit{}), pi, t, r, w, closes, obs))
    case I.NextCall{a, b}:
      L.ex_false(K.Rule6(I.NextCall{a, b}, Source.environment(source), Source.artifact(source), I.Initialize{world, c, seed(Unit{}), pi}, t),
        succession_initial_and_impossible(source, c, world, seed(Unit{}), pi, t, a, b, obs))
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
    case I.CertificateAccepted{a0, a1, a2}: Unit{}
    case I.CertificateRejected{a0, a1}: Unit{}
    case I.ProgramStarted{a0, a1, a2}: Unit{}
    case I.Evaluated{a0, a1, a2, a3}: Unit{}
    case I.Prepared{a0, a1}: Unit{}
    case I.FailedEnvironment{a0, a1, a2}: Unit{}
    case I.DeliveredEverything{a0}: Unit{}
    case I.DeliveryInterrupted{a0}: Unit{}
    case I.ClosedChannel{}: Unit{}

def rule6_service(~source: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~pi: String, +world: Nat, +reception: X.Reception, +t: Nat, f: I.Fact,
  origin: PublicationService.OriginOfMoment(source, c, seed, history, world, Scenarios.Service{reception}),
  obs: I.Happens(Source.environment(source), Source.artifact(source),
    I.Serve{world, c, History.state(history(world), seed(Unit{})), reception}, t, f)) ->
  K.Rule6(f, Source.environment(source), Source.artifact(source),
    I.Serve{world, c, History.state(history(world), seed(Unit{})), reception}, t):
  match f:
    case I.Published{w}: PublicationService.publication_by_moment(source, c, seed, history, pi, world, Scenarios.Service{reception}, t, w, origin, obs)
    case I.StateVisible{w}: Vis.visibility_service_source_obeys_rule6(source, c, world, History.state(history(world), seed(Unit{})), reception, t, w, obs)
    case I.Concluded{r, w, closes}: conclusion_of_source_obeys_rule6(source, c, world, History.state(history(world), seed(Unit{})), reception, t, r, w, closes, obs)
    case I.NextCall{a, b}: succession_of_source_obeys_rule6(source, c, world, History.state(history(world), seed(Unit{})), reception, t, a, b, obs)
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
    case I.CertificateAccepted{a0, a1, a2}: Unit{}
    case I.CertificateRejected{a0, a1}: Unit{}
    case I.ProgramStarted{a0, a1, a2}: Unit{}
    case I.Evaluated{a0, a1, a2, a3}: Unit{}
    case I.Prepared{a0, a1}: Unit{}
    case I.FailedEnvironment{a0, a1, a2}: Unit{}
    case I.DeliveredEverything{a0}: Unit{}
    case I.DeliveryInterrupted{a0}: Unit{}
    case I.ClosedChannel{}: Unit{}

def rule6_in_moment(~source: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~pi: String, +world: Nat, +moment: Scenarios.Moment,
  +t: Nat, f: I.Fact, origin: PublicationService.OriginOfMoment(source, c, seed, history, world, moment),
  obs: I.Happens(Source.environment(source), Source.artifact(source), Scenarios.of_moment(c, seed, history, pi, moment, world), t, f)) ->
  K.Rule6(f, Source.environment(source), Source.artifact(source), Scenarios.of_moment(c, seed, history, pi, moment, world), t):
  match moment:
    case Scenarios.Initialization{}: rule6_initial(source, c, seed, history, pi, world, t, f, origin, obs)
    case Scenarios.Service{r}: rule6_service(source, c, seed, history, pi, world, r, t, f, origin, obs)

def fact_in_moment(~source: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~pi: String, +world: Nat, +moment: Scenarios.Moment,
  -t: Nat, -f: I.Fact,
  canonical: {Source.scenario(source, world) == Scenarios.of_moment(c, seed, history, pi, moment, world) : I.Scenario},
  observed: Source.of_route(source, Source.scenario(source, world), t, f)) ->
  I.Happens(Source.environment(source), Source.artifact(source), Scenarios.of_moment(c, seed, history, pi, moment, world), t, f):
  match moment:
    case Scenarios.Initialization{}:
      Source.introduce_fact_literal(source, Source.artifact(source), I.Initialize{world, c, seed(Unit{}), pi}, t, f,
        L.Both{{==}, Source.origin_literal(source, I.Initialize{world, c, seed(Unit{}), pi}, Source.scenario(source, world), t, f,
          Equal.sym(I.Scenario, Source.scenario(source, world), I.Initialize{world, c, seed(Unit{}), pi}, canonical), observed)})
    case Scenarios.Service{+r}:
      Source.introduce_fact_literal(source, Source.artifact(source), I.Serve{world, c, History.state(history(world), seed(Unit{})), r}, t, f,
        L.Both{{==}, Source.origin_literal(source, I.Serve{world, c, History.state(history(world), seed(Unit{})), r}, Source.scenario(source, world), t, f,
          Equal.sym(I.Scenario, Source.scenario(source, world), I.Serve{world, c, History.state(history(world), seed(Unit{})), r}, canonical), observed)})

def rule6_of_origin(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String,
  -x: I.Scenario, +world: Nat, +t: Nat, f: I.Fact,
  origin: PublicationService.OriginOfMoment(Model.source(base, c, seed, history, moment, pi), c, seed, history, world, moment(world)),
  observed: L.E<{Source.artifact(Model.source(base, c, seed, history, moment, pi)) == Source.artifact(Model.source(base, c, seed, history, moment, pi)) : String},
    L.E<{x == Source.scenario(Model.source(base, c, seed, history, moment, pi), world) : I.Scenario},
      Source.of_route(Model.source(base, c, seed, history, moment, pi), Source.scenario(Model.source(base, c, seed, history, moment, pi), world), t, f)>>) ->
  K.Rule6(f, Source.environment(Model.source(base, c, seed, history, moment, pi)), Source.artifact(Model.source(base, c, seed, history, moment, pi)), x, t):
  match observed:
    case L.Both{name, L.Both{equal, raw}}:
      %Equal.sym(I.Scenario, x, Scenarios.canonical(c, seed, history, moment, pi, world),
        Equal.trans(I.Scenario, x, Source.scenario(Model.source(base, c, seed, history, moment, pi), world),
          Scenarios.canonical(c, seed, history, moment, pi, world), equal, Model.scenario_of_model(base, c, seed, history, moment, pi, world))) :
        K.Rule6(f, Source.environment(Model.source(base, c, seed, history, moment, pi)), Source.artifact(Model.source(base, c, seed, history, moment, pi)), _, t)
      rule6_in_moment(Model.source(base, c, seed, history, moment, pi), c, seed, history, pi, world, moment(world), t, f, origin,
        fact_in_moment(Model.source(base, c, seed, history, moment, pi), c, seed, history, pi, world, moment(world), t, f,
          Model.scenario_of_model(base, c, seed, history, moment, pi, world), raw))

def law6_of_scenario(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String,
  origins: @m: Nat -> PublicationService.OriginOfMoment(Model.source(base, c, seed, history, moment, pi), c, seed, history, m, moment(m)),
  x: I.Scenario, +t: Nat, f: I.Fact,
  observed: I.Happens(Source.environment(Model.source(base, c, seed, history, moment, pi)), Source.artifact(Model.source(base, c, seed, history, moment, pi)), x, t, f)) ->
  K.Rule6(f, Source.environment(Model.source(base, c, seed, history, moment, pi)), Source.artifact(Model.source(base, c, seed, history, moment, pi)), x, t):
  match x:
    case I.Initialize{+m, original, +s, +proof}:
      rule6_of_origin(base, c, seed, history, moment, pi, I.Initialize{m, original, s, proof}, m, t, f, origins(m),
        Source.eliminate_fact(Model.source(base, c, seed, history, moment, pi), Source.artifact(Model.source(base, c, seed, history, moment, pi)), I.Initialize{m, original, s, proof}, t, f, observed))
    case I.Serve{+m, original, +s, +reception}:
      rule6_of_origin(base, c, seed, history, moment, pi, I.Serve{m, original, s, reception}, m, t, f, origins(m),
        Source.eliminate_fact(Model.source(base, c, seed, history, moment, pi), Source.artifact(Model.source(base, c, seed, history, moment, pi)), I.Serve{m, original, s, reception}, t, f, observed))

def law6_of_model(~base: Source.Source, ~c: S.Configuration, ~seed: Unit -> D.State,
  ~history: Nat -> List<&2, History.Record>, ~moment: Nat -> Scenarios.Moment, ~pi: String,
  origins: @m: Nat -> PublicationService.OriginOfMoment(Model.source(base, c, seed, history, moment, pi), c, seed, history, m, moment(m))) ->
  K.Law6(Source.environment(Model.source(base, c, seed, history, moment, pi)), Source.artifact(Model.source(base, c, seed, history, moment, pi))):
  x => +t => f => observed => law6_of_scenario(base, c, seed, history, moment, pi, origins, x, t, f, observed)
