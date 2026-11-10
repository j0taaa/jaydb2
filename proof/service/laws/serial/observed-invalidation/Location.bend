# Preparation phase locations in an actual retained serial block. The only
# extra data facts identify its same script Job and actual decoder result;
# exact block generation and every global query are derived from Engine.run.
import Base
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Resources.bend as X
import ../../../../../contract/Semantics.bend as S
import ../../../../ProtocolService.bend as Q
import ../../../../SourceService.bend as Source
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/InvalidationPhases.bend as N
import ../../../model/EventObserver.bend as O
import ../../../model/FrameBounds.bend as B
import ../../../model/serial/Engine.bend as Engine
import ../../../model/serial/Chain.bend as Chain
import ../../../model/serial/Decode.bend as Decode
import ../../../model/serial/Dispatch.bend as Dispatch
import ./Prelude.bend as Prelude
import ../../../model/serial/GeneratedBlocks.bend as Generated


def world_successor(block: Engine.Block) -> {Succ{Chain.block_ordinal(block)} == Engine.world(block) : Nat}:
  match block:
    case Engine.Block{ordinal, selected, input, before, run}: {==}


def source_equation(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +block: Engine.Block, +input: X.Reception, +primitives: Dispatch.Primitives,
  +raw: P.Request, +frames: List<&2, Q.Frame>,
  generated: Generated.HeadSource(c, binding, public, block, Engine.Job{input, primitives}),
  decoded: {Decode.run(c, E.database(Chain.block_before(block)), input) ==
    Decode.DecodeRun{Decode.Parsed{W.Extension{W.Invalidate{}, raw}}, frames} : Decode.DecodeRun}) ->
  {Engine.block_items(block) == Prelude.source(c, Engine.world(block), input, Chain.block_before(block), raw, Prelude.cleanup(primitives), Dispatch.send(primitives), frames) : List<&2, O.Item>}:
  Equal.trans(List<&2, O.Item>, Engine.block_items(block),
    Engine.block_items(Engine.block(c, binding, public, Chain.block_ordinal(block), Chain.block_before(block), Engine.Job{input, primitives})),
    Prelude.source(c, Engine.world(block), input, Chain.block_before(block), raw, Prelude.cleanup(primitives), Dispatch.send(primitives), frames),
    Equal.cong(Engine.Block, List<&2, O.Item>, Engine.block_items, block,
      Engine.block(c, binding, public, Chain.block_ordinal(block), Chain.block_before(block), Engine.Job{input, primitives}), generated),
    (%world_successor(block) :
      {Engine.block_items(Engine.block(c, binding, public, Chain.block_ordinal(block), Chain.block_before(block), Engine.Job{input, primitives})) ==
        Prelude.source(c, _, input, Chain.block_before(block), raw, Prelude.cleanup(primitives), Dispatch.send(primitives), frames) : List<&2, O.Item>}
      Prelude.actual_decoded_invalidation_block_retains_selection_and_every_codec_and_phase_event(c, binding, public,
        Chain.block_ordinal(block), Chain.block_before(block), input, raw, frames, primitives, decoded)))


def source_query(~c: S.Configuration, +block: Engine.Block, +input: X.Reception, +primitives: Dispatch.Primitives,
  +raw: P.Request, +frames: List<&2, Q.Frame>, +index: Nat, +phase: N.InvalidationEvent,
  source: {Engine.block_items(block) == Prelude.source(c, Engine.world(block), input, Chain.block_before(block), raw, Prelude.cleanup(primitives), Dispatch.send(primitives), frames) : List<&2, O.Item>},
  phase_found: {B.query(N.InvalidationEvent, N.events(N.run(c, Chain.block_before(block), raw, Prelude.cleanup(primitives), Dispatch.send(primitives))), index) == Some{phase} : Maybe<&2, N.InvalidationEvent>}) ->
  {B.query(O.Item, Engine.block_items(block), Prelude.phase_index(frames, index)) == Some{O.Item{Engine.world(block), E.database(Chain.block_before(block)), input, O.Invalidation{phase}}} : Maybe<&2, O.Item>}:
  Equal.trans(Maybe<&2, O.Item>, B.query(O.Item, Engine.block_items(block), Prelude.phase_index(frames, index)),
    B.query(O.Item, Prelude.source(c, Engine.world(block), input, Chain.block_before(block), raw, Prelude.cleanup(primitives), Dispatch.send(primitives), frames), Prelude.phase_index(frames, index)),
    Some{O.Item{Engine.world(block), E.database(Chain.block_before(block)), input, O.Invalidation{phase}}},
    Equal.cong(List<&2, O.Item>, Maybe<&2, O.Item>, items => B.query(O.Item, items, Prelude.phase_index(frames, index)), Engine.block_items(block),
      Prelude.source(c, Engine.world(block), input, Chain.block_before(block), raw, Prelude.cleanup(primitives), Dispatch.send(primitives), frames), source),
    Prelude.every_actual_invalidation_phase_query_retains_its_exact_measured_codec_offset(c, Engine.world(block), input, Chain.block_before(block), raw, Prelude.cleanup(primitives), Dispatch.send(primitives), frames, index, phase, phase_found))
