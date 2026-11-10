# A relevant observation of one actual call cannot migrate into another
# retained block, including after publications by earlier calls. Exact Item
# queries, positions and all same-slot RelFact alternatives are retained.
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

import ./ObservationLocation.bend as Location
import ../../model/ItemWorlds.bend as Clock
import ../../model/serial/BlockNames.bend as Names


def scenario_world(~c: S.Configuration, +item: O.Item) -> {E.scenario_world(O.scenario(c, item)) == Clock.world(item) : Nat}:
  match item:
    case O.Item{world, selected, input, event}: {==}

def same_world(~c: S.Configuration, -x: I.Scenario, +block: Engine.Block, +other: Engine.Block,
  +item: O.Item, local: Nat,
  known: {E.scenario_world(x) == Engine.world(block) : Nat},
  scenario: {x == O.scenario(c, item) : I.Scenario},
  query: {B.query(O.Item, Engine.block_items(other), local) == Some{item} : Maybe<&2, O.Item>}) ->
  {Engine.world(block) == Engine.world(other) : Nat}:
  Equal.trans(Nat, Engine.world(block), E.scenario_world(x), Engine.world(other),
    Equal.sym(Nat, E.scenario_world(x), Engine.world(block), known),
    Equal.trans(Nat, E.scenario_world(x), E.scenario_world(O.scenario(c, item)), Engine.world(other),
      Equal.cong(I.Scenario, Nat, E.scenario_world, x, O.scenario(c, item), scenario),
      Equal.trans(Nat, E.scenario_world(O.scenario(c, item)), Clock.world(item), Engine.world(other),
        scenario_world(c, item), Items.every_actual_local_block_item_has_its_owning_call_world(other, local, item, query))))


def align(+blocks: List<&2, Engine.Block>, +owner: Nat, +other_owner: Nat, +block: Engine.Block, +other: Engine.Block,
  +global: Nat, +local: Nat, +item: O.Item,
  local_query: {B.query(O.Item, Engine.block_items(other), local) == Some{item} : Maybe<&2, O.Item>},
  position: {global == Nat.add(Items.prefix_size(blocks, other_owner), local) : Nat},
  same: L.E<{owner == other_owner : Nat}, {block == other : Engine.Block}>) ->
  L.E<{B.query(O.Item, Engine.block_items(block), local) == Some{item} : Maybe<&2, O.Item>},
    {global == Nat.add(Items.prefix_size(blocks, owner), local) : Nat}>:
  match same:
    case L.Both{same_owner, same_block}:
      L.Both{
        Equal.trans(Maybe<&2, O.Item>, B.query(O.Item, Engine.block_items(block), local), B.query(O.Item, Engine.block_items(other), local), Some{item},
          Equal.cong(Engine.Block, Maybe<&2, O.Item>, b => B.query(O.Item, Engine.block_items(b), local), block, other, same_block), local_query),
        Equal.trans(Nat, global, Nat.add(Items.prefix_size(blocks, other_owner), local), Nat.add(Items.prefix_size(blocks, owner), local), position,
          Equal.cong(Nat, Nat, i => Nat.add(Items.prefix_size(blocks, i), local), other_owner, owner, Equal.sym(Nat, owner, other_owner, same_owner)))}


def Located(~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~c: S.Configuration,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~script: List<&2, Engine.Job>, ~instance: String,
  -x: I.Scenario, +at: Nat, -f: E.Fact, +owner: Nat, +block: Engine.Block) -> Type:
  &global: Nat -> &item: O.Item -> &local: Nat ->
    L.E<{at == O.time(global) : Nat},
      L.E<{B.query(O.Item, Engine.items(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), global) == Some{item} : Maybe<&2, O.Item>},
        L.E<{B.query(O.Item, Engine.block_items(block), local) == Some{item} : Maybe<&2, O.Item>},
          L.E<{global == Nat.add(Items.prefix_size(Engine.blocks(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), owner), local) : Nat}, O.RelFact(c, binding, public, O.event(item), f)>>>>

def finish(~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~c: S.Configuration,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~script: List<&2, Engine.Job>, ~instance: String,
  -x: I.Scenario, +at: Nat, -f: E.Fact, +owner: Nat, +block: Engine.Block, +global: Nat, +item: O.Item, +local: Nat,
  time: {at == O.time(global) : Nat},
  query: {B.query(O.Item, Engine.items(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), global) == Some{item} : Maybe<&2, O.Item>},
  relation: O.RelFact(c, binding, public, O.event(item), f),
  aligned: L.E<{B.query(O.Item, Engine.block_items(block), local) == Some{item} : Maybe<&2, O.Item>},
    {global == Nat.add(Items.prefix_size(Engine.blocks(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), owner), local) : Nat}>) -> Located(binding, public, c, seed, pi, artifacts, script, instance, x, at, f, owner, block):
  match aligned:
    case L.Both{local_query, position}: (global, item, local, L.Both{time, L.Both{query, L.Both{local_query, L.Both{position, relation}}}})


def from_location(~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~c: S.Configuration,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~script: List<&2, Engine.Job>, ~instance: String,
  -x: I.Scenario, +at: Nat, -f: E.Fact, +owner: Nat, +block: Engine.Block,
  known_at: {B.query(Engine.Block, Engine.blocks(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), owner) == Some{block} : Maybe<&2, Engine.Block>},
  known_world: {E.scenario_world(x) == Engine.world(block) : Nat},
  found: Location.Located(c, binding, public, script, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, x, at, f)) -> Located(binding, public, c, seed, pi, artifacts, script, instance, x, at, f, owner, block):
  match found:
    case (+global, +item, L.Both{time, L.Both{global_query, L.Both{scenario, L.Both{relation,
      (+other_owner, +other, +local, L.Both{other_at, L.Both{+local_query, position}})}}}}):
      finish(binding, public, c, seed, pi, artifacts, script, instance, x, at, f, owner, block, global, item, local, time, global_query, relation,
        align(Engine.blocks(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), owner, other_owner, block, other, global, local, item, local_query, position,
          Names.one_actual_call_world_identifies_one_retained_block_index_and_complete_block_payload(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, owner, other_owner,
            block, other, known_at, other_at, same_world(c, x, block, other, item, local, known_world, scenario, local_query))))

law every_relevant_same_call_observation_is_located_in_the_same_actual_retained_block:
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
  for +owner: Nat
  for +block: Engine.Block
  for known_at: {B.query(Engine.Block, Engine.blocks(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), owner) == Some{block} : Maybe<&2, Engine.Block>}
  for known_world: {E.scenario_world(x) == Engine.world(block) : Nat}
  for relevant: U.Relevant(U.view(f))
  for observed: E.observes(O.environment(binding, public, c, seed, pi, artifacts, Engine.items(Engine.run(c, binding, public, script, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), instance), Source.artifact(binding), x, at, f)
  Located(binding, public, c, seed, pi, artifacts, script, instance, x, at, f, owner, block)
def every_relevant_same_call_observation_is_located_in_the_same_actual_retained_block(binding, public, c, seed, pi, artifacts, script, instance, x, at, f, owner, block, known_at, known_world, relevant, observed):
  from_location(binding, public, c, seed, pi, artifacts, script, instance, x, at, f, owner, block, known_at, known_world,
    Location.every_relevant_actual_serial_observation_retains_its_exact_item_call_origin_and_all_cofacts(binding, public, c, seed, pi, artifacts, script, instance, x, at, f, relevant, observed))
