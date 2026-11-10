# Preparation phase locations in an actual retained serial block. The only
# extra data facts identify its same script Job and actual decoder result;
# exact block generation and every global query are derived from Engine.run.
import Base
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Resources.bend as X
import ../../../../../contract/Semantics.bend as S
import ../../../../Foundations.bend as F
import ../../../../ProtocolService.bend as Q
import ../../../../SourceService.bend as Source
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../model/EventObserver.bend as O
import ../../../model/FrameBounds.bend as B
import ../../../model/serial/Engine.bend as Engine
import ../../../model/serial/Chain.bend as Chain
import ../../../model/serial/Decode.bend as Decode
import ../../../model/serial/Dispatch.bend as Dispatch
import ../../../model/serial/PreparationPrelude.bend as Prelude
import ../../../model/serial/SerialItems.bend as Items
import ../../../model/serial/GeneratedBlocks.bend as Generated


def known_job(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +script: List<&2, Engine.Job>, +owner: Nat, +block: Engine.Block, +job: Engine.Job,
  found: {B.query(Engine.Job, script, owner) == Some{job} : Maybe<&2, Engine.Job>},
  generated: Generated.GeneratedAt(c, binding, public, script, owner, block)) -> Generated.HeadSource(c, binding, public, block, job):
  match generated:
    case (other, L.Both{original, source}):
      %F.some_injective(Engine.Job, other, job,
        Equal.trans(Maybe<&2, Engine.Job>, Some{other}, B.query(Engine.Job, script, owner), Some{job},
          Equal.sym(Maybe<&2, Engine.Job>, B.query(Engine.Job, script, owner), Some{other}, original), found)) :
        Generated.HeadSource(c, binding, public, block, _)
      source


def world_successor(block: Engine.Block) -> {Succ{Chain.block_ordinal(block)} == Engine.world(block) : Nat}:
  match block:
    case Engine.Block{ordinal, selected, input, before, run}: {==}


def source_equation(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +block: Engine.Block, +input: X.Reception, +primitives: Dispatch.Primitives,
  +mode: V.Mode, +raw: P.Request, +frames: List<&2, Q.Frame>,
  generated: Generated.HeadSource(c, binding, public, block, Engine.Job{input, primitives}),
  decoded: {Decode.run(c, E.database(Chain.block_before(block)), input) ==
    Decode.DecodeRun{Decode.Parsed{W.Extension{V.operation(mode), raw}}, frames} : Decode.DecodeRun}) ->
  {Engine.block_items(block) == Prelude.source(c, Engine.world(block), input, Chain.block_before(block), mode, raw, Prelude.returns(primitives), frames) : List<&2, O.Item>}:
  Equal.trans(List<&2, O.Item>, Engine.block_items(block),
    Engine.block_items(Engine.block(c, binding, public, Chain.block_ordinal(block), Chain.block_before(block), Engine.Job{input, primitives})),
    Prelude.source(c, Engine.world(block), input, Chain.block_before(block), mode, raw, Prelude.returns(primitives), frames),
    Equal.cong(Engine.Block, List<&2, O.Item>, Engine.block_items, block,
      Engine.block(c, binding, public, Chain.block_ordinal(block), Chain.block_before(block), Engine.Job{input, primitives}), generated),
    (%world_successor(block) :
      {Engine.block_items(Engine.block(c, binding, public, Chain.block_ordinal(block), Chain.block_before(block), Engine.Job{input, primitives})) ==
        Prelude.source(c, _, input, Chain.block_before(block), mode, raw, Prelude.returns(primitives), frames) : List<&2, O.Item>}
      Prelude.actual_decoded_preparation_block_retains_selection_and_every_codec_and_phase_event(c, binding, public,
        Chain.block_ordinal(block), Chain.block_before(block), input, mode, raw, frames, primitives, decoded)))


law an_actual_preparation_block_recovers_its_exact_codec_and_phase_source_from_its_same_script_job:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +script: List<&2, Engine.Job>
  for +initial_ordinal: Nat
  for +initial: E.Snapshot
  for +owner: Nat
  for +block: Engine.Block
  for +input: X.Reception
  for +primitives: Dispatch.Primitives
  for +mode: V.Mode
  for +raw: P.Request
  for +frames: List<&2, Q.Frame>
  for block_found: {B.query(Engine.Block, Engine.blocks(Engine.run(c, binding, public, script, initial_ordinal, initial)), owner) == Some{block} : Maybe<&2, Engine.Block>}
  for job_found: {B.query(Engine.Job, script, owner) == Some{Engine.Job{input, primitives}} : Maybe<&2, Engine.Job>}
  for decoded: {Decode.run(c, E.database(Chain.block_before(block)), input) == Decode.DecodeRun{Decode.Parsed{W.Extension{V.operation(mode), raw}}, frames} : Decode.DecodeRun}
  {Engine.block_items(block) == Prelude.source(c, Engine.world(block), input, Chain.block_before(block), mode, raw, Prelude.returns(primitives), frames) : List<&2, O.Item>}
def an_actual_preparation_block_recovers_its_exact_codec_and_phase_source_from_its_same_script_job(c, binding, public, script, initial_ordinal, initial, owner, block, input, primitives, mode, raw, frames, block_found, job_found, decoded):
  source_equation(c, binding, public, block, input, primitives, mode, raw, frames,
    known_job(c, binding, public, script, owner, block, Engine.Job{input, primitives}, job_found,
      Generated.every_actual_block_query_recovers_its_same_actual_script_job_and_computed_dispatch(c, binding, public, script, initial_ordinal, initial, owner, block, block_found)), decoded)


def source_query(~c: S.Configuration, +block: Engine.Block, +input: X.Reception, +primitives: Dispatch.Primitives,
  +mode: V.Mode, +raw: P.Request, +frames: List<&2, Q.Frame>, +index: Nat, +phase: V.PreparationEvent,
  source: {Engine.block_items(block) == Prelude.source(c, Engine.world(block), input, Chain.block_before(block), mode, raw, Prelude.returns(primitives), frames) : List<&2, O.Item>},
  phase_found: {B.query(V.PreparationEvent, V.events(V.run(c, mode, raw, Chain.block_before(block), Prelude.returns(primitives))), index) == Some{phase} : Maybe<&2, V.PreparationEvent>}) ->
  {B.query(O.Item, Engine.block_items(block), Prelude.phase_index(frames, index)) == Some{O.Item{Engine.world(block), E.database(Chain.block_before(block)), input, O.Preparation{phase}}} : Maybe<&2, O.Item>}:
  Equal.trans(Maybe<&2, O.Item>, B.query(O.Item, Engine.block_items(block), Prelude.phase_index(frames, index)),
    B.query(O.Item, Prelude.source(c, Engine.world(block), input, Chain.block_before(block), mode, raw, Prelude.returns(primitives), frames), Prelude.phase_index(frames, index)),
    Some{O.Item{Engine.world(block), E.database(Chain.block_before(block)), input, O.Preparation{phase}}},
    Equal.cong(List<&2, O.Item>, Maybe<&2, O.Item>, items => B.query(O.Item, items, Prelude.phase_index(frames, index)), Engine.block_items(block),
      Prelude.source(c, Engine.world(block), input, Chain.block_before(block), mode, raw, Prelude.returns(primitives), frames), source),
    Prelude.every_actual_preparation_phase_query_retains_its_exact_measured_codec_offset(c, Engine.world(block), input, Chain.block_before(block), mode, raw, Prelude.returns(primitives), frames, index, phase, phase_found))


law every_queried_actual_preparation_phase_has_the_same_exact_global_item_with_its_real_codec_offset:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +script: List<&2, Engine.Job>
  for +initial_ordinal: Nat
  for +initial: E.Snapshot
  for +owner: Nat
  for +block: Engine.Block
  for +input: X.Reception
  for +primitives: Dispatch.Primitives
  for +mode: V.Mode
  for +raw: P.Request
  for +frames: List<&2, Q.Frame>
  for +index: Nat
  for +phase: V.PreparationEvent
  for +block_found: {B.query(Engine.Block, Engine.blocks(Engine.run(c, binding, public, script, initial_ordinal, initial)), owner) == Some{block} : Maybe<&2, Engine.Block>}
  for job_found: {B.query(Engine.Job, script, owner) == Some{Engine.Job{input, primitives}} : Maybe<&2, Engine.Job>}
  for decoded: {Decode.run(c, E.database(Chain.block_before(block)), input) == Decode.DecodeRun{Decode.Parsed{W.Extension{V.operation(mode), raw}}, frames} : Decode.DecodeRun}
  for phase_found: {B.query(V.PreparationEvent, V.events(V.run(c, mode, raw, Chain.block_before(block), Prelude.returns(primitives))), index) == Some{phase} : Maybe<&2, V.PreparationEvent>}
  {B.query(O.Item, Engine.items(Engine.run(c, binding, public, script, initial_ordinal, initial)),
      Nat.add(Items.prefix_size(Engine.blocks(Engine.run(c, binding, public, script, initial_ordinal, initial)), owner), Prelude.phase_index(frames, index))) ==
    Some{O.Item{Engine.world(block), E.database(Chain.block_before(block)), input, O.Preparation{phase}}} : Maybe<&2, O.Item>}
def every_queried_actual_preparation_phase_has_the_same_exact_global_item_with_its_real_codec_offset(c, binding, public, script, initial_ordinal, initial, owner, block, input, primitives, mode, raw, frames, index, phase, block_found, job_found, decoded, phase_found):
  Items.an_actual_retained_block_local_item_query_recovers_the_same_engine_global_item(c, binding, public, script, initial_ordinal, initial, owner, block, Prelude.phase_index(frames, index),
    O.Item{Engine.world(block), E.database(Chain.block_before(block)), input, O.Preparation{phase}}, block_found,
    source_query(c, block, input, primitives, mode, raw, frames, index, phase,
      an_actual_preparation_block_recovers_its_exact_codec_and_phase_source_from_its_same_script_job(c, binding, public, script, initial_ordinal, initial, owner, block, input, primitives, mode, raw, frames, block_found, job_found, decoded), phase_found))
