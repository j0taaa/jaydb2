# Recover the SAME indexed Job and reached artifact seal cause from an actual
# retained block query. Coordinator selection is retained and cannot pretend
# to be a artifact seal.
import Base
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/Resources.bend as X
import ../../../../../contract/Semantics.bend as S
import ../../../../SourceService.bend as Source
import ../../../specification/ServiceLaws.bend as E
import ../../../model/EventObserver.bend as O
import ../../../model/FrameBounds.bend as B
import ../../../model/serial/Common.bend as C
import ../../../model/serial/Decode.bend as Decode
import ../../../model/serial/Dispatch.bend as Dispatch
import ../../../model/serial/Engine.bend as Engine
import ../../../model/serial/Chain.bend as Chain
import ../../../model/serial/GeneratedBlocks.bend as Generated
import ../observed-headers/BlockLayout.bend as Block
import ./SealingData.bend as Data
import ./Observation.bend as Observation
import ./DispatchSites.bend as Sites


def All(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +block: Engine.Block, -primitives: Dispatch.Primitives) -> Type:
  Sites.All(c, Chain.block_before(block), Decode.decision(Decode.run(c, E.database(Chain.block_before(block)), Block.input(block))), primitives, Block.events(block))


def selected_prefix(-c: S.Configuration, +before: E.Snapshot, -decision: Decode.Decision, -primitives: Dispatch.Primitives,
  selected: Bool, +events: List<&2, O.AuditEvent>, body: Sites.All(c, before, decision, primitives, events)) -> Sites.All(c, before, decision, primitives, Engine.selected_events(selected, before, events)):
  match selected:
    case False{}: body
    case True{}: L.Both{Unit{}, body}


def computed(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +ordinal: Nat, +before: E.Snapshot, +input: X.Reception, +primitives: Dispatch.Primitives) ->
  All(c, binding, public, Engine.block(c, binding, public, ordinal, before, Engine.Job{input, primitives}), primitives):
  selected_prefix(c, before, Decode.decision(Decode.run(c, E.database(before), input)), primitives, Engine.selection(X.decide_reception(c, input)),
    C.events(Dispatch.run(c, binding, public, before, input, primitives)),
    Sites.every_actual_dispatch_seal_event_has_its_original_reached_preparation_cause(c, binding, public, before, input, primitives))


def from_source(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +block: Engine.Block, +input: X.Reception, +primitives: Dispatch.Primitives,
  source: Generated.HeadSource(c, binding, public, block, Engine.Job{input, primitives})) -> All(c, binding, public, block, primitives):
  %Equal.sym(Engine.Block, block, Engine.block(c, binding, public, Chain.block_ordinal(block), Chain.block_before(block), Engine.Job{input, primitives}), source) : All(c, binding, public, _, primitives)
  computed(c, binding, public, Chain.block_ordinal(block), Chain.block_before(block), input, primitives)


def Hit(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, -script: List<&2, Engine.Job>, -owner: Nat, +block: Engine.Block, -f: E.Fact) -> Type:
  &input: X.Reception -> &primitives: Dispatch.Primitives ->
    L.E<{B.query(Engine.Job, script, owner) == Some{Engine.Job{input, primitives}} : Maybe<&2, Engine.Job>},
      L.E<Generated.HeadSource(c, binding, public, block, Engine.Job{input, primitives}),
        Sites.ViewClaim(c, Chain.block_before(block), Decode.decision(Decode.run(c, E.database(Chain.block_before(block)), Block.input(block))), primitives, Data.fact(f))>>


def with_job(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, -script: List<&2, Engine.Job>, +owner: Nat, +block: Engine.Block, +index: Nat, +event: O.AuditEvent, -f: E.Fact,
  +input: X.Reception, +primitives: Dispatch.Primitives,
  job_found: {B.query(Engine.Job, script, owner) == Some{Engine.Job{input, primitives}} : Maybe<&2, Engine.Job>},
  +source: {block == Engine.block(c, binding, public, Chain.block_ordinal(block), Chain.block_before(block), Engine.Job{input, primitives}) : Engine.Block},
  relevant: Data.Relevant(Data.fact(f)),
  found: {B.query(O.AuditEvent, Block.events(block), index) == Some{event} : Maybe<&2, O.AuditEvent>},
  relation: O.RelFact(c, binding, public, event, f)) -> Hit(c, binding, public, script, owner, block, f):
  (input, primitives, L.Both{job_found, L.Both{source,
    (%Observation.actual_event_view(c, binding, public, event, f, relevant, relation) :
      Sites.ViewClaim(c, Chain.block_before(block), Decode.decision(Decode.run(c, E.database(Chain.block_before(block)), Block.input(block))), primitives, _)
    Sites.query(c, Chain.block_before(block), Decode.decision(Decode.run(c, E.database(Chain.block_before(block)), Block.input(block))), primitives,
      Block.events(block), index, event, from_source(c, binding, public, block, input, primitives, source), found))}})


def with_source(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, -script: List<&2, Engine.Job>, +owner: Nat, +block: Engine.Block, +index: Nat, +event: O.AuditEvent, -f: E.Fact,
  relevant: Data.Relevant(Data.fact(f)),
  found: {B.query(O.AuditEvent, Block.events(block), index) == Some{event} : Maybe<&2, O.AuditEvent>},
  relation: O.RelFact(c, binding, public, event, f),
  generated: Generated.GeneratedAt(c, binding, public, script, owner, block)) -> Hit(c, binding, public, script, owner, block, f):
  match generated:
    case (Engine.Job{input, primitives}, L.Both{job_found, source}):
      with_job(c, binding, public, script, owner, block, index, event, f, input, primitives, job_found, source, relevant, found, relation)


law every_actual_sealing_block_recovers_its_same_indexed_job_and_reached_reached_preparation_sealing_data:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +script: List<&2, Engine.Job>
  for +initial_ordinal: Nat
  for +initial: E.Snapshot
  for +owner: Nat
  for +block: Engine.Block
  for +index: Nat
  for +event: O.AuditEvent
  for -f: E.Fact
  for relevant: Data.Relevant(Data.fact(f))
  for block_found: {B.query(Engine.Block, Engine.blocks(Engine.run(c, binding, public, script, initial_ordinal, initial)), owner) == Some{block} : Maybe<&2, Engine.Block>}
  for found: {B.query(O.AuditEvent, Block.events(block), index) == Some{event} : Maybe<&2, O.AuditEvent>}
  for relation: O.RelFact(c, binding, public, event, f)
  Hit(c, binding, public, script, owner, block, f)
def every_actual_sealing_block_recovers_its_same_indexed_job_and_reached_reached_preparation_sealing_data(c, binding, public, script, initial_ordinal, initial, owner, block, index, event, f, relevant, block_found, found, relation):
  with_source(c, binding, public, script, owner, block, index, event, f, relevant, found, relation,
    Generated.every_actual_block_query_recovers_its_same_actual_script_job_and_computed_dispatch(c, binding, public, script, initial_ordinal, initial, owner, block, block_found))
