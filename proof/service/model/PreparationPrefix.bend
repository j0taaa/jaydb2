# Exact early-prefix Current and query APIs for actual preparation dispatch.
# No checker acceptance, validity, target law or native trace is a premise.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Interface.bend as I
import ../../../contract/Logic.bend as L
import ../../../contract/PreparedLaws.bend as H
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/Protocol.bend as P
import ../../../contract/Resources.bend as X
import ../../../contract/Semantics.bend as S
import ../../Foundations.bend as F
import ../../SourceService.bend as Source
import ../specification/ServiceLaws.bend as E
import ../phases/PreparePhases.bend as V
import ./EventObserver.bend as O
import ./EventHistory.bend as T
import ./CurrentWitness.bend as C
import ./PreparationCurrent.bend as A
import ./FrameBounds.bend as B

def header(+mode: V.Mode, +raw: P.Request, identity: Maybe<&2, D.Context>, tail: V.PreparationRun) -> V.PreparationRun:
  V.push(V.WireReceived{W.Extension{V.operation(mode), raw}}, V.push(V.IdentityEstablished{W.Extension{V.operation(mode), raw}, identity}, tail))

def PrefixProperties(-items: List<&2, O.Item>, +before: E.Snapshot, +count: Nat) -> Type:
  L.E<T.Coherent(T.take(count, items), before),
    L.E<{T.finish(T.take(count, items), before) == before : E.Snapshot},
      {B.count(O.Item, T.take(count, items)) == count : Nat}>>

def header_prefix_properties(+world: Nat, +input: X.Reception, +before: E.Snapshot,
  mode: V.Mode, raw: P.Request, identity: Maybe<&2, D.Context>, count: Nat,
  tail: V.PreparationRun, bounded: {Nat.is_le(count, 3n) == True{} : Bool}) ->
  PrefixProperties(A.with_run(world, input, before, header(mode, raw, identity, tail)), before, count):
  match count:
    case 0n: L.Both{Unit{}, L.Both{{==}, {==}}}
    case 1n+m:
      match m:
        case 0n: L.Both{L.Both{Unit{}, Unit{}}, L.Both{{==}, {==}}}
        case 1n+n:
          match n:
            case 0n:
              match tail:
                case V.PreparationRun{events, result, snapshot, waiting, closed}:
                  L.Both{L.Both{Unit{}, L.Both{Unit{}, Unit{}}}, L.Both{{==}, {==}}}
            case 1n+r:
              match r:
                case 0n:
                  match tail:
                    case V.PreparationRun{events, result, snapshot, waiting, closed}:
                      L.Both{L.Both{Unit{}, L.Both{Unit{}, L.Both{Unit{}, Unit{}}}}, L.Both{{==}, {==}}}
                case 1n+k:
                  L.ex_false(PrefixProperties(A.with_run(world, input, before, header(mode, raw, identity, tail)), before, Succ{Succ{Succ{Succ{k}}}}), F.false_negative_true(bounded))

law the_actual_dispatch_header_derives_all_first_three_prefix_properties:
  for ~c: S.Configuration
  for +world: Nat
  for +input: X.Reception
  for +before: E.Snapshot
  for +mode: V.Mode
  for +raw: P.Request
  for returns: V.Returns
  for count: Nat
  for bounded: {Nat.is_le(count, 3n) == True{} : Bool}
  PrefixProperties(A.source(c, world, input, before, mode, raw, returns), before, count)
def the_actual_dispatch_header_derives_all_first_three_prefix_properties(c, world, input, before, mode, raw, returns, count, bounded):
  header_prefix_properties(world, input, before, mode, raw, D.authenticate(E.database(before), I.credential(raw)), count,
    V.authenticated(c, D.authenticate(E.database(before), I.credential(raw)), mode, raw, before, returns), bounded)

def CurrentAtSnapshot(~a: E.Environment, ~c: S.Configuration, -k: String, -world: Nat, -input: X.Reception, -count: Nat, +snapshot: E.Snapshot) -> Type:
  E.Current(a, k, I.Serve{world, c, E.database(snapshot), input}, O.time(count), snapshot)

def current_from_header_properties(~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~c: S.Configuration,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~items: List<&2, O.Item>, ~instance: String,
  -world: Nat, -input: X.Reception, +count: Nat,
  properties: PrefixProperties(items, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, count)) ->
  CurrentAtSnapshot(O.environment(binding, public, c, seed, pi, artifacts, items, instance), c, Source.artifact(binding),
    world, input, count, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}):
  match properties:
    case L.Both{coherent, L.Both{snapshot_same, count_same}}:
      %snapshot_same : CurrentAtSnapshot(O.environment(binding, public, c, seed, pi, artifacts, items, instance), c, Source.artifact(binding), world, input, count, _)
      %count_same : CurrentAtSnapshot(O.environment(binding, public, c, seed, pi, artifacts, items, instance), c, Source.artifact(binding), world, input, _,
        T.finish(T.take(count, items), E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}))
      C.complete_current_is_derived_from_the_lossless_operational_event_prefix(binding, public, c, seed, pi, artifacts, items, instance,
        T.take(count, items), T.drop(count, items), world, input, coherent,
        Equal.sym(List<&2, O.Item>, T.append(T.take(count, items), T.drop(count, items)), items,
          T.taking_a_prefix_preserves_every_event_in_its_full_suffix(count, items)))

law every_actual_early_preparation_prefix_has_full_current_history:
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~c: S.Configuration
  for ~seed: Unit -> D.State
  for ~pi: String
  for ~artifacts: H.Artifacts
  for ~instance: String
  for ~world: Nat
  for ~input: X.Reception
  for ~mode: V.Mode
  for ~raw: P.Request
  for ~returns: V.Returns
  for +count: Nat
  for bounded: {Nat.is_le(count, 3n) == True{} : Bool}
  CurrentAtSnapshot(O.environment(binding, public, c, seed, pi, artifacts,
    A.source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw, returns), instance), c, Source.artifact(binding),
    world, input, count, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})
def every_actual_early_preparation_prefix_has_full_current_history(binding, public, c, seed, pi, artifacts, instance, world, input, mode, raw, returns, count, bounded):
  current_from_header_properties(binding, public, c, seed, pi, artifacts,
    A.source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw, returns), instance, world, input, count,
    the_actual_dispatch_header_derives_all_first_three_prefix_properties(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw, returns, count, bounded))

def header_queries(+mode: V.Mode, +raw: P.Request, +identity: Maybe<&2, D.Context>, tail: V.PreparationRun) ->
  L.E<{B.query(V.PreparationEvent, V.events(header(mode, raw, identity, tail)), 0n) == Some{V.WireReceived{W.Extension{V.operation(mode), raw}}} : Maybe<&2, V.PreparationEvent>},
    {B.query(V.PreparationEvent, V.events(header(mode, raw, identity, tail)), 1n) == Some{V.IdentityEstablished{W.Extension{V.operation(mode), raw}, identity}} : Maybe<&2, V.PreparationEvent>}>:
  match tail:
    case V.PreparationRun{events, result, snapshot, waiting, closed}: L.Both{{==}, {==}}

law actual_dispatcher_has_the_exact_wire_and_identity_queries:
  for ~c: S.Configuration
  for +mode: V.Mode
  for +raw: P.Request
  for +before: E.Snapshot
  for returns: V.Returns
  L.E<{B.query(V.PreparationEvent, V.events(V.run(c, mode, raw, before, returns)), 0n) == Some{V.WireReceived{W.Extension{V.operation(mode), raw}}} : Maybe<&2, V.PreparationEvent>},
    {B.query(V.PreparationEvent, V.events(V.run(c, mode, raw, before, returns)), 1n) == Some{V.IdentityEstablished{W.Extension{V.operation(mode), raw}, D.authenticate(E.database(before), I.credential(raw))}} : Maybe<&2, V.PreparationEvent>}>
def actual_dispatcher_has_the_exact_wire_and_identity_queries(c, mode, raw, before, returns):
  header_queries(mode, raw, D.authenticate(E.database(before), I.credential(raw)),
    V.authenticated(c, D.authenticate(E.database(before), I.credential(raw)), mode, raw, before, returns))

law actual_source_selects_the_exact_snapshot_at_zero:
  for ~c: S.Configuration
  for -world: Nat
  for -input: X.Reception
  for -before: E.Snapshot
  for -mode: V.Mode
  for -raw: P.Request
  for -returns: V.Returns
  {B.query(O.Item, A.source(c, world, input, before, mode, raw, returns), 0n) ==
    Some{O.Item{world, E.database(before), input, O.Selection{before}}} : Maybe<&2, O.Item>}
def actual_source_selects_the_exact_snapshot_at_zero(c, world, input, before, mode, raw, returns):
  {==}

def item_result(+world: Nat, +selected: D.State, +input: X.Reception, result: Maybe<&2, V.PreparationEvent>) -> Maybe<&2, O.Item>:
  match result:
    case None{}: None{}
    case Some{phase}: Some{O.Item{world, selected, input, O.Preparation{phase}}}

law exact_phase_query_lifts_to_the_full_observer_item_query:
  for +world: Nat
  for +selected: D.State
  for +input: X.Reception
  for phases: List<&2, V.PreparationEvent>
  for index: Nat
  {B.query(O.Item, A.phase_items(world, selected, input, phases), index) ==
    item_result(world, selected, input, B.query(V.PreparationEvent, phases, index)) : Maybe<&2, O.Item>}
def exact_phase_query_lifts_to_the_full_observer_item_query(world, selected, input, phases, index):
  match phases index:
    case Nil{} _: {==}
    case Con{phase, rest} 0n: {==}
    case Con{phase, rest} 1n+k: exact_phase_query_lifts_to_the_full_observer_item_query(world, selected, input, rest, k)

law exact_dispatcher_phase_query_supplies_the_actual_observer_query:
  for ~c: S.Configuration
  for +world: Nat
  for +input: X.Reception
  for +before: E.Snapshot
  for mode: V.Mode
  for raw: P.Request
  for returns: V.Returns
  for +index: Nat
  for -phase: V.PreparationEvent
  for query: {B.query(V.PreparationEvent, V.events(V.run(c, mode, raw, before, returns)), index) == Some{phase} : Maybe<&2, V.PreparationEvent>}
  {B.query(O.Item, A.source(c, world, input, before, mode, raw, returns), Succ{index}) ==
    Some{O.Item{world, E.database(before), input, O.Preparation{phase}}} : Maybe<&2, O.Item>}
def exact_dispatcher_phase_query_supplies_the_actual_observer_query(c, world, input, before, mode, raw, returns, index, phase, query):
  Equal.trans(Maybe<&2, O.Item>, B.query(O.Item, A.phase_items(world, E.database(before), input, V.events(V.run(c, mode, raw, before, returns))), index),
    item_result(world, E.database(before), input, B.query(V.PreparationEvent, V.events(V.run(c, mode, raw, before, returns)), index)),
    Some{O.Item{world, E.database(before), input, O.Preparation{phase}}},
    exact_phase_query_lifts_to_the_full_observer_item_query(world, E.database(before), input, V.events(V.run(c, mode, raw, before, returns)), index),
    Equal.cong(Maybe<&2, V.PreparationEvent>, Maybe<&2, O.Item>, result => item_result(world, E.database(before), input, result),
      B.query(V.PreparationEvent, V.events(V.run(c, mode, raw, before, returns)), index), Some{phase}, query))

law a_real_query_constructs_the_exact_full_observation:
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~c: S.Configuration
  for ~seed: Unit -> D.State
  for ~pi: String
  for ~artifacts: H.Artifacts
  for ~items: List<&2, O.Item>
  for ~instance: String
  for +index: Nat
  for +item: O.Item
  for query: {B.query(O.Item, items, index) == Some{item} : Maybe<&2, O.Item>}
  E.observes(O.environment(binding, public, c, seed, pi, artifacts, items, instance), Source.artifact(binding),
    O.scenario(c, item), O.time(index), O.fact(c, binding, public, O.event(item)))
def a_real_query_constructs_the_exact_full_observation(binding, public, c, seed, pi, artifacts, items, instance, index, item, query):
  L.Both{{==}, L.Right{(index, item, L.Both{{==}, L.Both{query, L.Both{{==}, L.Left{{==}}}}})}}

law a_real_earlier_query_constructs_the_exact_full_before_fact:
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~c: S.Configuration
  for ~seed: Unit -> D.State
  for ~pi: String
  for ~artifacts: H.Artifacts
  for ~items: List<&2, O.Item>
  for ~instance: String
  for +index: Nat
  for +item: O.Item
  for -at: Nat
  for query: {B.query(O.Item, items, index) == Some{item} : Maybe<&2, O.Item>}
  for earlier: {Nat.is_lt(O.time(index), at) == True{} : Bool}
  E.Before(O.environment(binding, public, c, seed, pi, artifacts, items, instance), Source.artifact(binding),
    O.scenario(c, item), at, O.fact(c, binding, public, O.event(item)))
def a_real_earlier_query_constructs_the_exact_full_before_fact(binding, public, c, seed, pi, artifacts, items, instance, index, item, at, query, earlier):
  (O.time(index), L.Both{earlier, a_real_query_constructs_the_exact_full_observation(binding, public, c, seed, pi, artifacts, items, instance, index, item, query)})
