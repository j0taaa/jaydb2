# Actual complete owning block, including its optional coordinator Selection,
# derives Shape from the same script Job. No source or trace table is supplied.
import Base
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/Resources.bend as X
import ../../../../../contract/Semantics.bend as S
import ../../../../SourceService.bend as Source
import ../../../specification/ServiceLaws.bend as E
import ../../../model/EventObserver.bend as O
import ../../../model/FrameBounds.bend as B
import ../../../model/serial/Common.bend as C
import ../../../model/serial/Dispatch.bend as Dispatch
import ../../../model/serial/Engine.bend as Engine
import ../../../model/serial/Chain.bend as Chain
import ../../../model/serial/GeneratedBlocks.bend as Generated
import ../observed-headers/BlockLayout.bend as Block
import ./Meaning.bend as M
import ./Algebra.bend as A
import ./DispatchSource.bend as Actual

def selection(selected: Bool, +before: E.Snapshot, +events: List<&2, O.AuditEvent>, shape: M.Shape<events>) ->
  M.Shape<Engine.selected_events(selected, before, events)>:
  match selected:
    case False{}: shape
    case True{}: A.prepend([O.Selection{before}], events, {==}, shape)

def computed(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +ordinal: Nat, +before: E.Snapshot, job: Engine.Job) ->
  M.Shape<Block.events(Engine.block(c, binding, public, ordinal, before, job))>:
  match job:
    case Engine.Job{+input, +primitives}:
      selection(Engine.selection(X.decide_reception(c, input)), before, C.events(Dispatch.run(c, binding, public, before, input, primitives)),
        Actual.every_actual_dispatch_derives_exact_unique_conclusion_and_its_own_prior_preparation(c, binding, public, before, input, primitives))

def generated(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  -script: List<&2, Engine.Job>, -owner: Nat, +block: Engine.Block, source: Generated.GeneratedAt(c, binding, public, script, owner, block)) -> M.Shape<Block.events(block)>:
  match source:
    case (+job, L.Both{job_query, exact}):
      %Equal.sym(Engine.Block, block, Engine.block(c, binding, public, Chain.block_ordinal(block), Chain.block_before(block), job), exact) : M.Shape<Block.events(_)>
      computed(c, binding, public, Chain.block_ordinal(block), Chain.block_before(block), job)

law every_actual_retained_block_derives_its_complete_shared_conclusion_shape:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +script: List<&2, Engine.Job>
  for +ordinal: Nat
  for +initial: E.Snapshot
  for +owner: Nat
  for +block: Engine.Block
  for found: {B.query(Engine.Block, Engine.blocks(Engine.run(c, binding, public, script, ordinal, initial)), owner) == Some{block} : Maybe<&2, Engine.Block>}
  M.Shape<Block.events(block)>
def every_actual_retained_block_derives_its_complete_shared_conclusion_shape(c, binding, public, script, ordinal, initial, owner, block, found):
  generated(c, binding, public, script, owner, block,
    Generated.every_actual_block_query_recovers_its_same_actual_script_job_and_computed_dispatch(c, binding, public, script, ordinal, initial, owner, block, found))
