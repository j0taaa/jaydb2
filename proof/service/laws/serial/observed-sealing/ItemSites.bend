# Exact original Item/RelFact -> same Job and reached cached resolution cause.
# The original full fact relation is retained for later Program equality;
# the DATA view never replaces it or becomes the observer.
import Base
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/Semantics.bend as S
import ../../../../SourceService.bend as Source
import ../../../specification/ServiceLaws.bend as E
import ../../../model/EventObserver.bend as O
import ../../../model/FrameBounds.bend as B
import ../../../model/serial/Engine.bend as Engine
import ../../../model/serial/Chain.bend as Chain
import ../../../model/serial/SerialItems.bend as Items
import ../observed-headers/BlockLayout.bend as Block
import ./SealingData.bend as Data
import ./Observation.bend as Observation
import ./BlockSites.bend as Sites


def Hit(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, -script: List<&2, Engine.Job>, -owner: Nat, +block: Engine.Block, -index: Nat, -item: O.Item, -f: E.Fact) -> Type:
  &event: O.AuditEvent ->
    L.E<{item == O.Item{Engine.world(block), E.database(Chain.block_before(block)), Block.input(block), event} : O.Item},
      L.E<O.RelFact(c, binding, public, event, f), Sites.Hit(c, binding, public, script, owner, block, f)>>


def with_relations(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +script: List<&2, Engine.Job>, +initial_ordinal: Nat, +initial: E.Snapshot,
  +owner: Nat, +block: Engine.Block, +index: Nat, -item: O.Item, +event: O.AuditEvent, -f: E.Fact,
  block_found: {B.query(Engine.Block, Engine.blocks(Engine.run(c, binding, public, script, initial_ordinal, initial)), owner) == Some{block} : Maybe<&2, Engine.Block>},
  audit_found: {B.query(O.AuditEvent, Block.events(block), index) == Some{event} : Maybe<&2, O.AuditEvent>},
  exact: {item == O.Item{Engine.world(block), E.database(Chain.block_before(block)), Block.input(block), event} : O.Item},
  relevant: Data.Relevant(Data.fact(f)),
  relations: L.E<O.RelFact(c, binding, public, event, f), O.RelFact(c, binding, public, event, f)>) -> Hit(c, binding, public, script, owner, block, index, item, f):
  match relations:
    case L.Both{first, second}:
      (event, L.Both{exact, L.Both{second,
        Sites.every_actual_sealing_block_recovers_its_same_indexed_job_and_reached_reached_preparation_sealing_data(c, binding, public, script, initial_ordinal, initial, owner, block, index, event, f, relevant, block_found, audit_found, first)}})


def with_relevance(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +script: List<&2, Engine.Job>, +initial_ordinal: Nat, +initial: E.Snapshot,
  +owner: Nat, +block: Engine.Block, +index: Nat, +item: O.Item, +event: O.AuditEvent, -f: E.Fact,
  block_found: {B.query(Engine.Block, Engine.blocks(Engine.run(c, binding, public, script, initial_ordinal, initial)), owner) == Some{block} : Maybe<&2, Engine.Block>},
  audit_found: {B.query(O.AuditEvent, Block.events(block), index) == Some{event} : Maybe<&2, O.AuditEvent>},
  exact: {item == O.Item{Engine.world(block), E.database(Chain.block_before(block)), Block.input(block), event} : O.Item},
  relation: O.RelFact(c, binding, public, event, f),
  relevance: L.E<Data.Relevant(Data.fact(f)), Data.Relevant(Data.fact(f))>) -> Hit(c, binding, public, script, owner, block, index, item, f):
  match relevance:
    case L.Both{first, second}:
      with_relations(c, binding, public, script, initial_ordinal, initial, owner, block, index, item, event, f, block_found, audit_found, exact, second,
        Observation.duplicate_relevant_actual_relation(c, binding, public, event, f, first, relation))


def from_stamp(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +script: List<&2, Engine.Job>, +initial_ordinal: Nat, +initial: E.Snapshot,
  +owner: Nat, +block: Engine.Block, +index: Nat, +item: O.Item, -f: E.Fact,
  block_found: {B.query(Engine.Block, Engine.blocks(Engine.run(c, binding, public, script, initial_ordinal, initial)), owner) == Some{block} : Maybe<&2, Engine.Block>},
  relevant: L.E<Data.Relevant(Data.fact(f)), Data.Relevant(Data.fact(f))>, relation: O.RelFact(c, binding, public, O.event(item), f),
  origin: Items.StampedHit(Engine.world(block), Block.input(block), E.database(Chain.block_before(block)), Block.events(block), index, item)) -> Hit(c, binding, public, script, owner, block, index, item, f):
  match origin:
    case (+event, L.Both{audit_found, +exact}):
      with_relevance(c, binding, public, script, initial_ordinal, initial, owner, block, index, item, event, f, block_found, audit_found, exact,
        (%Equal.cong(O.Item, O.AuditEvent, O.event, item, O.Item{Engine.world(block), E.database(Chain.block_before(block)), Block.input(block), event}, exact) : O.RelFact(c, binding, public, _, f) relation),
        relevant)


def from_block(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +script: List<&2, Engine.Job>, +initial_ordinal: Nat, +initial: E.Snapshot,
  +owner: Nat, +block: Engine.Block, +index: Nat, +item: O.Item, -f: E.Fact,
  block_found: {B.query(Engine.Block, Engine.blocks(Engine.run(c, binding, public, script, initial_ordinal, initial)), owner) == Some{block} : Maybe<&2, Engine.Block>},
  relevant: L.E<Data.Relevant(Data.fact(f)), Data.Relevant(Data.fact(f))>, relation: O.RelFact(c, binding, public, O.event(item), f),
  origin: Items.BlockEventHit(block, index, item)) -> Hit(c, binding, public, script, owner, block, index, item, f):
  match block:
    case Engine.Block{+ordinal, +selected, +input, +before, +run}:
      from_stamp(c, binding, public, script, initial_ordinal, initial, owner, Engine.Block{ordinal, selected, input, before, run}, index, item, f, block_found, relevant, relation, origin)


law every_actual_sealing_item_recovers_its_original_full_relation_same_indexed_job_and_reached_cause:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +script: List<&2, Engine.Job>
  for +initial_ordinal: Nat
  for +initial: E.Snapshot
  for +owner: Nat
  for +block: Engine.Block
  for +index: Nat
  for +item: O.Item
  for -f: E.Fact
  for relevant: L.E<Data.Relevant(Data.fact(f)), Data.Relevant(Data.fact(f))>
  for block_found: {B.query(Engine.Block, Engine.blocks(Engine.run(c, binding, public, script, initial_ordinal, initial)), owner) == Some{block} : Maybe<&2, Engine.Block>}
  for item_found: {B.query(O.Item, Engine.block_items(block), index) == Some{item} : Maybe<&2, O.Item>}
  for relation: O.RelFact(c, binding, public, O.event(item), f)
  Hit(c, binding, public, script, owner, block, index, item, f)
def every_actual_sealing_item_recovers_its_original_full_relation_same_indexed_job_and_reached_cause(c, binding, public, script, initial_ordinal, initial, owner, block, index, item, f, relevant, block_found, item_found, relation):
  from_block(c, binding, public, script, initial_ordinal, initial, owner, block, index, item, f, block_found, relevant, relation,
    Items.an_actual_block_item_query_recovers_its_same_exact_local_source_event_and_origin(block, index, item, item_found))
