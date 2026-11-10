# Same physical call before/observed facts, retaining every prior block and codec frame.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/PreparedLaws.bend as H
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Resources.bend as X
import ../../../../../contract/Semantics.bend as S
import ../../../../ProtocolService.bend as Q
import ../../../../SourceService.bend as Source
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/InvalidationPhases.bend as N
import ../../../model/EventObserver.bend as O
import ../../../model/FrameBounds.bend as B
import ../../../model/PreparationPrefix.bend as Prefix
import ../../../model/TimeEmbedding.bend as Time
import ../../../model/serial/Engine.bend as Engine
import ../../../model/serial/Chain.bend as Chain
import ../../../model/serial/Dispatch.bend as Dispatch
import ./Prelude.bend as Prelude
import ../../../model/serial/SerialItems.bend as Items
import ../header/History.bend as History
import ./Location.bend as Location


def phases_ordered(+prefix: Nat, +frames: List<&2, Q.Frame>, +early: Nat, +later: Nat,
  ordered: {Nat.is_lt(early, later) == True{} : Bool}) ->
  {Nat.is_lt(O.time(Nat.add(prefix, Prelude.phase_index(frames, early))), O.time(Nat.add(prefix, Prelude.phase_index(frames, later)))) == True{} : Bool}:
  Time.adding_prefix_preserves_strict_order(prefix, Prelude.phase_index(frames, early), Prelude.phase_index(frames, later),
    Time.adding_prefix_preserves_strict_order(B.count(Q.Frame, frames), early, later, ordered))


def selection_ordered(prefix: Nat, frames: List<&2, Q.Frame>, later: Nat) ->
  {Nat.is_lt(O.time(Nat.add(prefix, 0n)), O.time(Nat.add(prefix, Prelude.phase_index(frames, later)))) == True{} : Bool}:
  Time.adding_prefix_preserves_strict_order(prefix, 0n, Prelude.phase_index(frames, later), {==})


def phase_before(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  +owner: Nat, +block: Engine.Block, +input: X.Reception, +primitives: Dispatch.Primitives,
  +raw: P.Request, +frames: List<&2, Q.Frame>, +early: Nat, +later: Nat, +phase: N.InvalidationEvent,
  block_found: {B.query(Engine.Block, History.blocks(c, binding, public, script, seed, instance), owner) == Some{block} : Maybe<&2, Engine.Block>},
  source: {Engine.block_items(block) == Prelude.source(c, Engine.world(block), input, Chain.block_before(block), raw, Prelude.cleanup(primitives), Dispatch.send(primitives), frames) : List<&2, O.Item>},
  found: {B.query(N.InvalidationEvent, N.events(N.run(c, Chain.block_before(block), raw, Prelude.cleanup(primitives), Dispatch.send(primitives))), early) == Some{phase} : Maybe<&2, N.InvalidationEvent>},
  ordered: {Nat.is_lt(early, later) == True{} : Bool}) ->
  E.Before(History.environment(c, binding, public, script, seed, pi, artifacts, instance), Source.artifact(binding),
    I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), input},
    O.time(History.position(c, binding, public, script, seed, instance, owner, Prelude.phase_index(frames, later))), N.fact(c, binding, public, phase)):
  Prefix.a_real_earlier_query_constructs_the_exact_full_before_fact(binding, public, c, seed, pi, artifacts,
    History.items(c, binding, public, script, seed, instance), instance,
    History.position(c, binding, public, script, seed, instance, owner, Prelude.phase_index(frames, early)),
    O.Item{Engine.world(block), E.database(Chain.block_before(block)), input, O.Invalidation{phase}},
    O.time(History.position(c, binding, public, script, seed, instance, owner, Prelude.phase_index(frames, later))),
    Items.an_actual_retained_block_local_item_query_recovers_the_same_engine_global_item(c, binding, public, script, 0n, History.boot(seed, instance), owner, block, Prelude.phase_index(frames, early),
      O.Item{Engine.world(block), E.database(Chain.block_before(block)), input, O.Invalidation{phase}}, block_found,
      Location.source_query(c, block, input, primitives, raw, frames, early, phase, source, found)),
    phases_ordered(Items.prefix_size(History.blocks(c, binding, public, script, seed, instance), owner), frames, early, later, ordered))


def with_run_head(+world: Nat, +input: X.Reception, +before: E.Snapshot, raw: P.Request, frames: List<&2, Q.Frame>, run: N.InvalidationRun) ->
  {B.query(O.Item, Prelude.with_run(world, input, before, raw, frames, run), 0n) == Some{O.Item{world, E.database(before), input, O.Selection{before}}} : Maybe<&2, O.Item>}:
  match run:
    case N.InvalidationRun{events, result, snapshot, waiting, closed}: {==}


def selection_query(~c: S.Configuration, +block: Engine.Block, +input: X.Reception, +primitives: Dispatch.Primitives,
  +raw: P.Request, +frames: List<&2, Q.Frame>,
  source: {Engine.block_items(block) == Prelude.source(c, Engine.world(block), input, Chain.block_before(block), raw, Prelude.cleanup(primitives), Dispatch.send(primitives), frames) : List<&2, O.Item>}) ->
  {B.query(O.Item, Engine.block_items(block), 0n) == Some{O.Item{Engine.world(block), E.database(Chain.block_before(block)), input, O.Selection{Chain.block_before(block)}}} : Maybe<&2, O.Item>}:
  Equal.trans(Maybe<&2, O.Item>, B.query(O.Item, Engine.block_items(block), 0n),
    B.query(O.Item, Prelude.source(c, Engine.world(block), input, Chain.block_before(block), raw, Prelude.cleanup(primitives), Dispatch.send(primitives), frames), 0n),
    Some{O.Item{Engine.world(block), E.database(Chain.block_before(block)), input, O.Selection{Chain.block_before(block)}}},
    Equal.cong(List<&2, O.Item>, Maybe<&2, O.Item>, items => B.query(O.Item, items, 0n), Engine.block_items(block),
      Prelude.source(c, Engine.world(block), input, Chain.block_before(block), raw, Prelude.cleanup(primitives), Dispatch.send(primitives), frames), source),
    with_run_head(Engine.world(block), input, Chain.block_before(block), raw, frames, N.run(c, Chain.block_before(block), raw, Prelude.cleanup(primitives), Dispatch.send(primitives))))


def selected_before(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  +owner: Nat, +block: Engine.Block, +input: X.Reception, +primitives: Dispatch.Primitives,
  +raw: P.Request, +frames: List<&2, Q.Frame>, +later: Nat,
  block_found: {B.query(Engine.Block, History.blocks(c, binding, public, script, seed, instance), owner) == Some{block} : Maybe<&2, Engine.Block>},
  source: {Engine.block_items(block) == Prelude.source(c, Engine.world(block), input, Chain.block_before(block), raw, Prelude.cleanup(primitives), Dispatch.send(primitives), frames) : List<&2, O.Item>}) ->
  E.SelectedBefore(History.environment(c, binding, public, script, seed, pi, artifacts, instance), Source.artifact(binding),
    I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), input},
    O.time(History.position(c, binding, public, script, seed, instance, owner, Prelude.phase_index(frames, later))), Chain.block_before(block)):
  Prefix.a_real_earlier_query_constructs_the_exact_full_before_fact(binding, public, c, seed, pi, artifacts, History.items(c, binding, public, script, seed, instance), instance,
    History.position(c, binding, public, script, seed, instance, owner, 0n), O.Item{Engine.world(block), E.database(Chain.block_before(block)), input, O.Selection{Chain.block_before(block)}},
    O.time(History.position(c, binding, public, script, seed, instance, owner, Prelude.phase_index(frames, later))),
    Items.an_actual_retained_block_local_item_query_recovers_the_same_engine_global_item(c, binding, public, script, 0n, History.boot(seed, instance), owner, block, 0n,
      O.Item{Engine.world(block), E.database(Chain.block_before(block)), input, O.Selection{Chain.block_before(block)}}, block_found,
      selection_query(c, block, input, primitives, raw, frames, source)),
    selection_ordered(Items.prefix_size(History.blocks(c, binding, public, script, seed, instance), owner), frames, later))


def phase_observed(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  +owner: Nat, +block: Engine.Block, +input: X.Reception, +primitives: Dispatch.Primitives,
  +raw: P.Request, +frames: List<&2, Q.Frame>, +index: Nat, +phase: N.InvalidationEvent,
  block_found: {B.query(Engine.Block, History.blocks(c, binding, public, script, seed, instance), owner) == Some{block} : Maybe<&2, Engine.Block>},
  source: {Engine.block_items(block) == Prelude.source(c, Engine.world(block), input, Chain.block_before(block), raw, Prelude.cleanup(primitives), Dispatch.send(primitives), frames) : List<&2, O.Item>},
  found: {B.query(N.InvalidationEvent, N.events(N.run(c, Chain.block_before(block), raw, Prelude.cleanup(primitives), Dispatch.send(primitives))), index) == Some{phase} : Maybe<&2, N.InvalidationEvent>}) ->
  E.observes(History.environment(c, binding, public, script, seed, pi, artifacts, instance), Source.artifact(binding),
    I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), input},
    O.time(History.position(c, binding, public, script, seed, instance, owner, Prelude.phase_index(frames, index))), N.fact(c, binding, public, phase)):
  Prefix.a_real_query_constructs_the_exact_full_observation(binding, public, c, seed, pi, artifacts, History.items(c, binding, public, script, seed, instance), instance,
    History.position(c, binding, public, script, seed, instance, owner, Prelude.phase_index(frames, index)),
    O.Item{Engine.world(block), E.database(Chain.block_before(block)), input, O.Invalidation{phase}},
    Items.an_actual_retained_block_local_item_query_recovers_the_same_engine_global_item(c, binding, public, script, 0n, History.boot(seed, instance), owner, block, Prelude.phase_index(frames, index),
      O.Item{Engine.world(block), E.database(Chain.block_before(block)), input, O.Invalidation{phase}}, block_found,
      Location.source_query(c, block, input, primitives, raw, frames, index, phase, source, found)))
