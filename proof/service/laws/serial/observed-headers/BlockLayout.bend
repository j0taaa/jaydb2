# The actual block adds only its actual optional coordinator Selection. The
# same indexed Job and literal computed dispatch are recovered from Engine.
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
import ../../../model/serial/CallIds.bend as Names
import ../../../model/serial/GeneratedBlocks.bend as Generated
import ./Layout.bend as Layout


def input(block: Engine.Block) -> X.Reception:
  Engine.Block{ordinal, selected, input, before, run} = block
  input


def events(+block: Engine.Block) -> List<&2, O.AuditEvent>:
  Engine.selected_events(Names.selected(block), Chain.block_before(block), C.events(Chain.block_run(block)))


def Shape(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +block: Engine.Block) -> Type:
  Layout.Choice(Chain.block_before(block), Decode.decision(Decode.run(c, E.database(Chain.block_before(block)), input(block))), events(block))


def selected_prefix(+before: E.Snapshot, +decision: Decode.Decision, selected: Bool, +tail: List<&2, O.AuditEvent>,
  shape: Layout.Choice(before, decision, tail)) -> Layout.Choice(before, decision, Engine.selected_events(selected, before, tail)):
  match selected:
    case False{}: shape
    case True{}: Layout.prefix_choice(before, decision, [O.Selection{before}], tail, L.Both{Unit{}, Unit{}}, L.Both{{==}, Unit{}}, shape)


def computed(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +ordinal: Nat, +before: E.Snapshot, job: Engine.Job) ->
  Shape(c, binding, public, Engine.block(c, binding, public, ordinal, before, job)):
  match job:
    case Engine.Job{+input, +primitives}:
      selected_prefix(before, Decode.decision(Decode.run(c, E.database(before), input)), Engine.selection(X.decide_reception(c, input)),
        C.events(Dispatch.run(c, binding, public, before, input, primitives)),
        Layout.every_actual_dispatch_derives_the_exact_retained_header_grammar_or_proves_there_are_no_headers(c, binding, public, before, input, primitives))


def generated(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  -script: List<&2, Engine.Job>, -owner: Nat, +block: Engine.Block, source: Generated.GeneratedAt(c, binding, public, script, owner, block)) -> Shape(c, binding, public, block):
  match source:
    case (+job, L.Both{job_query, exact}):
      %Equal.sym(Engine.Block, block, Engine.block(c, binding, public, Chain.block_ordinal(block), Chain.block_before(block), job), exact) : Shape(c, binding, public, _)
      computed(c, binding, public, Chain.block_ordinal(block), Chain.block_before(block), job)


law every_actual_retained_block_derives_its_complete_header_grammar_and_real_decoder_decision:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +script: List<&2, Engine.Job>
  for +initial_ordinal: Nat
  for +initial: E.Snapshot
  for +owner: Nat
  for +block: Engine.Block
  for found: {B.query(Engine.Block, Engine.blocks(Engine.run(c, binding, public, script, initial_ordinal, initial)), owner) == Some{block} : Maybe<&2, Engine.Block>}
  Shape(c, binding, public, block)
def every_actual_retained_block_derives_its_complete_header_grammar_and_real_decoder_decision(c, binding, public, script, initial_ordinal, initial, owner, block, found):
  generated(c, binding, public, script, owner, block,
    Generated.every_actual_block_query_recovers_its_same_actual_script_job_and_computed_dispatch(c, binding, public, script, initial_ordinal, initial, owner, block, found))
