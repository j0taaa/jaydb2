# Lift a DERIVED unique tag of one actual call block through the entire
# mixed history. Other calls retain their publications and observations.
# AllPlain/OnlyTag are internal, local source properties, never external
# native uniqueness or a final law assumption.
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



import ./SameCallLocation.bend as Call


def finish(-blocks: List<&2, Engine.Block>, -owner: Nat, -point: Nat, -expected: U.View, -actual: U.View,
  -at: Nat, -global: Nat, -local: Nat,
  time: {at == O.time(global) : Nat},
  position: {global == Nat.add(Items.prefix_size(blocks, owner), local) : Nat},
  unique: L.E<{local == point : Nat}, {actual == expected : U.View}>) ->
  L.E<{at == O.time(Nat.add(Items.prefix_size(blocks, owner), point)) : Nat}, {actual == expected : U.View}>:
  match unique:
    case L.Both{same_index, same_value}:
      L.Both{Equal.trans(Nat, at, O.time(global), O.time(Nat.add(Items.prefix_size(blocks, owner), point)), time,
        Equal.cong(Nat, Nat, O.time, global, Nat.add(Items.prefix_size(blocks, owner), point),
          Equal.trans(Nat, global, Nat.add(Items.prefix_size(blocks, owner), local), Nat.add(Items.prefix_size(blocks, owner), point), position,
            Equal.cong(Nat, Nat, i => Nat.add(Items.prefix_size(blocks, owner), i), local, point, same_index)))), same_value}


def from_location(~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~c: S.Configuration,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~script: List<&2, Engine.Job>, ~instance: String,
  -x: I.Scenario, +at: Nat, -f: E.Fact, +owner: Nat, +block: Engine.Block,
  +kind: Nat, +point: Nat, -expected: U.View,
  plain: U.AllPlain(Engine.block_items(block)),
  unique: U.OnlyTag(kind, U.values(c, binding, public, Engine.block_items(block)), point, expected),
  wanted: {U.tag(U.view(f)) == kind : Nat},
  location: Call.Located(binding, public, c, seed, pi, artifacts, script, instance, x, at, f, owner, block)) -> L.E<{at == O.time(Nat.add(Items.prefix_size(Engine.blocks(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), owner), point)) : Nat}, {U.view(f) == expected : U.View}>:
  match location:
    case (+global, +item, +local, L.Both{time, L.Both{global_query, L.Both{local_query, L.Both{position, relation}}}}):
      finish(Engine.blocks(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), owner, point, expected, U.view(f), at, global, local, time, position,
        U.a_structurally_unique_source_tag_has_the_exact_index_and_payload(kind, U.values(c, binding, public, Engine.block_items(block)), point, local,
          expected, U.view(f), unique,
          U.observed_listed_view(c, binding, public, Engine.block_items(block), local, item, f, U.view(f), plain, local_query, {==}, relation), wanted))


def observed(~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~c: S.Configuration,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~script: List<&2, Engine.Job>, ~instance: String,
  -x: I.Scenario, +at: Nat, -f: E.Fact, +owner: Nat, +block: Engine.Block,
  +kind: Nat, +point: Nat, -expected: U.View,
  known_at: {B.query(Engine.Block, Engine.blocks(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), owner) == Some{block} : Maybe<&2, Engine.Block>},
  known_world: {E.scenario_world(x) == Engine.world(block) : Nat},
  plain: U.AllPlain(Engine.block_items(block)),
  unique: U.OnlyTag(kind, U.values(c, binding, public, Engine.block_items(block)), point, expected),
  relevant: U.Relevant(U.view(f)), wanted: {U.tag(U.view(f)) == kind : Nat},
  observation: E.observes(O.environment(binding, public, c, seed, pi, artifacts, Engine.items(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), instance), Source.artifact(binding), x, at, f)) -> L.E<{at == O.time(Nat.add(Items.prefix_size(Engine.blocks(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), owner), point)) : Nat}, {U.view(f) == expected : U.View}>:
  from_location(binding, public, c, seed, pi, artifacts, script, instance, x, at, f, owner, block, kind, point, expected, plain, unique, wanted,
    Call.every_relevant_same_call_observation_is_located_in_the_same_actual_retained_block(binding, public, c, seed, pi, artifacts, script, instance,
      x, at, f, owner, block, known_at, known_world, relevant, observation))
