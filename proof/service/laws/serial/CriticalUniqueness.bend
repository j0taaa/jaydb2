# Local uniqueness for selection/mutation/conclusion, preserving publication
# cofacts and requiring NO global or per-block AllPlain property. The actual
# source's local OnlyTag proof is derived separately by concrete builders.
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
import ./LocalUniqueness.bend as Local
import ./CriticalProjection.bend as Projection


def from_location(~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~c: S.Configuration,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~script: List<&2, Engine.Job>, ~instance: String,
  -x: I.Scenario, +at: Nat, -f: E.Fact, +owner: Nat, +block: Engine.Block,
  +kind: Projection.CriticalKind, +point: Nat, -expected: U.View,
  unique: U.OnlyTag(Projection.tag(kind), U.values(c, binding, public, Engine.block_items(block)), point, expected),
  +wanted: {U.tag(U.view(f)) == Projection.tag(kind) : Nat},
  location: Call.Located(binding, public, c, seed, pi, artifacts, script, instance, x, at, f, owner, block)) -> L.E<{at == O.time(Nat.add(Items.prefix_size(Engine.blocks(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), owner), point)) : Nat}, {U.view(f) == expected : U.View}>:
  match location:
    case (+global, +item, +local, L.Both{time, L.Both{global_query, L.Both{local_query, L.Both{position, relation}}}}):
      Local.finish(Engine.blocks(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), owner, point, expected, U.view(f), at, global, local, time, position,
        U.a_structurally_unique_source_tag_has_the_exact_index_and_payload(Projection.tag(kind), U.values(c, binding, public, Engine.block_items(block)), point, local,
          expected, U.view(f), unique,
          Projection.actual_query(c, binding, public, kind, Engine.block_items(block), local, item, f, wanted, local_query, relation), wanted))


def observed(~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~c: S.Configuration,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~script: List<&2, Engine.Job>, ~instance: String,
  -x: I.Scenario, +at: Nat, -f: E.Fact, +owner: Nat, +block: Engine.Block,
  +kind: Projection.CriticalKind, +point: Nat, -expected: U.View,
  known_at: {B.query(Engine.Block, Engine.blocks(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), owner) == Some{block} : Maybe<&2, Engine.Block>},
  known_world: {E.scenario_world(x) == Engine.world(block) : Nat},
  unique: U.OnlyTag(Projection.tag(kind), U.values(c, binding, public, Engine.block_items(block)), point, expected),
  relevant: U.Relevant(U.view(f)), wanted: {U.tag(U.view(f)) == Projection.tag(kind) : Nat},
  observation: E.observes(O.environment(binding, public, c, seed, pi, artifacts, Engine.items(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), instance), Source.artifact(binding), x, at, f)) -> L.E<{at == O.time(Nat.add(Items.prefix_size(Engine.blocks(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), owner), point)) : Nat}, {U.view(f) == expected : U.View}>:
  from_location(binding, public, c, seed, pi, artifacts, script, instance, x, at, f, owner, block, kind, point, expected, unique, wanted,
    Call.every_relevant_same_call_observation_is_located_in_the_same_actual_retained_block(binding, public, c, seed, pi, artifacts, script, instance,
      x, at, f, owner, block, known_at, known_world, relevant, observation))
