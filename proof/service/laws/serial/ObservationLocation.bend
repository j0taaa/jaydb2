# Recover the exact actual Item AND full RelFact from a relevant observation.
# Mixed histories may contain real publications, so no global AllPlain premise
# or canonical-fact-only projection is used. Same-slot cofacts remain intact.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Interface.bend as I
import ../../../../contract/Logic.bend as L
import ../../../../contract/PreparedLaws.bend as H
import ../../../../contract/Semantics.bend as S
import ../../../SourceService.bend as Source
import ../../specification/ServiceLaws.bend as E
import ../../model/EventObserver.bend as O
import ../../model/ObservationUniqueness.bend as U
import ../../model/serial/Engine.bend as Engine
import ../../model/FrameBounds.bend as B
import ../../model/serial/SerialItems.bend as Items

def listed(~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~c: S.Configuration,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~items: List<&2, O.Item>, ~instance: String,
  -x: I.Scenario, +at: Nat, -f: E.Fact, relevant: U.Relevant(U.view(f)),
  observed: E.observes(O.environment(binding, public, c, seed, pi, artifacts, items, instance), Source.artifact(binding), x, at, f)) ->
  O.ListedObserved(c, binding, public, items, x, at, f):
  match observed:
    case L.Both{artifact, L.Left{L.Both{scenario, initial}}}:
      L.ex_false(O.ListedObserved(c, binding, public, items, x, at, f),
        U.relevant_not_void(U.view(f), relevant, U.initial_view_is_void(c, seed, pi, instance, at, f, initial)))
    case L.Both{artifact, L.Right{actual}}: actual

def Located(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  ~script: List<&2, Engine.Job>, ~before: E.Snapshot, -x: I.Scenario, +at: Nat, -f: E.Fact) -> Type:
  &global: Nat -> &item: O.Item ->
    L.E<{at == O.time(global) : Nat},
      L.E<{B.query(O.Item, Engine.items(Engine.run(c, binding, public, script, 0n, before)), global) == Some{item} : Maybe<&2, O.Item>},
        L.E<{x == O.scenario(c, item) : I.Scenario},
          L.E<O.RelFact(c, binding, public, O.event(item), f),
            Items.Located(Engine.blocks(Engine.run(c, binding, public, script, 0n, before)), global, item)>>>>

def locate_listed(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  ~script: List<&2, Engine.Job>, ~before: E.Snapshot, -x: I.Scenario, +at: Nat, -f: E.Fact,
  actual: O.ListedObserved(c, binding, public, Engine.items(Engine.run(c, binding, public, script, 0n, before)), x, at, f)) ->
  Located(c, binding, public, script, before, x, at, f):
  match actual:
    case (+global, +item, L.Both{time, L.Both{+query, L.Both{scenario, relation}}}):
      (global, item, L.Both{time, L.Both{query, L.Both{scenario, L.Both{relation,
        Items.every_actual_engine_item_query_derives_its_exact_retained_block_and_local_item(c, binding, public, script, 0n, before, global, item, query)}}}})

law every_relevant_actual_serial_observation_retains_its_exact_item_call_origin_and_all_cofacts:
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~c: S.Configuration
  for ~seed: Unit -> D.State
  for ~pi: String
  for ~artifacts: H.Artifacts
  for ~script: List<&2, Engine.Job>
  for ~instance: String
  for -x: I.Scenario
  for +at: Nat
  for -f: E.Fact
  for relevant: U.Relevant(U.view(f))
  for observed: E.observes(O.environment(binding, public, c, seed, pi, artifacts,
    Engine.items(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), instance), Source.artifact(binding), x, at, f)
  Located(c, binding, public, script, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, x, at, f)
def every_relevant_actual_serial_observation_retains_its_exact_item_call_origin_and_all_cofacts(binding, public, c, seed, pi, artifacts, script, instance, x, at, f, relevant, observed):
  locate_listed(c, binding, public, script, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, x, at, f,
    listed(binding, public, c, seed, pi, artifacts, Engine.items(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), instance,
      x, at, f, relevant, observed))
