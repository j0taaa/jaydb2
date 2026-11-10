# Full Current at actual ReceiptPrepared phase TWO, strictly BEFORE removal.
# Arbitrary pending/fatal/failed/complete cleanup returns remain unconstrained.
# Complete history, original selection and every codec offset remain retained.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/PreparedLaws.bend as H
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/PreparedRegistry.bend as G
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Requirements.bend as R
import ../../../../../contract/Resources.bend as X
import ../../../../../contract/Semantics.bend as S
import ../../../../ProtocolService.bend as Q
import ../../../../SourceService.bend as Source
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../phases/InvalidationPhases.bend as N
import ../../../phases/InvalidationEvents.bend as Original
import ../../../model/FrameBounds.bend as B
import ../../../model/EventObserver.bend as O
import ../../../model/serial/Engine.bend as Engine
import ../../../model/serial/Chain.bend as Chain
import ../../../model/serial/Dispatch.bend as Dispatch
import ../observed-invalidation/Prelude.bend as Prelude
import ./InvalidationMilestones.bend as M
import ../PreludeReplay.bend as Replay
import ../../../model/InvalidationPrefix.bend as Phase
import ../../../model/EventHistory.bend as T
import ../../../model/serial/SliceCurrent.bend as Current
import ../../../model/serial/SerialItems.bend as Items
import ../header/History.bend as History
import ../observed-invalidation/Location.bend as Location


def prefix_snapshot(+world: Nat, +input: X.Reception, +before: E.Snapshot, +raw: P.Request, +context: D.Context, +bytes: List<&2, U32>, tail: N.InvalidationRun) ->
  {T.finish(T.take(3n, Phase.with_run(world, input, before, Original.removal_prefix(before, raw, context, bytes, tail))), before) == before : E.Snapshot}:
  match tail:
    case N.InvalidationRun{events, result, snapshot, waiting, closed}: {==}

def through_codec(+world: Nat, +input: X.Reception, +before: E.Snapshot, +raw: P.Request,
  +frames: List<&2, Q.Frame>, run: N.InvalidationRun) ->
  {T.finish(T.take(Prelude.phase_index(frames, 2n), Prelude.with_run(world, input, before, raw, frames, run)), before) ==
    T.finish(T.take(3n, Phase.with_run(world, input, before, run)), before) : E.Snapshot}:
  match run:
    case N.InvalidationRun{events, result, snapshot, waiting, closed}:
      Replay.through_codec(frames, world, input, before, raw, Phase.phase_items(world, E.database(before), input, events), 2n)

def actual_replay(~c: S.Configuration, +world: Nat, +input: X.Reception, +before: E.Snapshot,
  +raw: P.Request, +context: D.Context, +entry: G.Entry, +bytes: List<&2, U32>,
  +frames: List<&2, Q.Frame>, +cleanup: N.CleanupReturn, +send: V.SendReturn,
  authenticated: {D.authenticate(E.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
  empty: {String.eq(I.proof(raw), "") == True{} : Bool},
  found: {G.lookup(E.instance(before), I.code(raw), E.registry(before)) == Some{entry} : Maybe<&2, G.Entry>},
  fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})) == True{} : Bool},
  frame: {W.frame_receipt(W.InvalidatedReceipt{}) == Some{bytes} : Maybe<&2, List<&2, U32>>}) ->
  {T.finish(T.take(Prelude.phase_index(frames, 2n), Prelude.source(c, world, input, before, raw, cleanup, send, frames)), before) == before : E.Snapshot}:
  Equal.trans(E.Snapshot,
    T.finish(T.take(Prelude.phase_index(frames, 2n), Prelude.source(c, world, input, before, raw, cleanup, send, frames)), before),
    T.finish(T.take(3n, Phase.source(c, world, input, before, raw, cleanup, send)), before), before,
    through_codec(world, input, before, raw, frames, N.run(c, before, raw, cleanup, send)),
    (%Equal.sym(N.InvalidationRun, N.run(c, before, raw, cleanup, send), Original.removal_prefix(before, raw, context, bytes, N.cleaned(cleanup, N.removed(before, I.code(raw)), bytes, send)),
      Original.actual_authorized_framed_invalidation_has_its_exact_removal_phases(c, before, raw, entry, context, bytes, cleanup, send, authenticated, empty, found, fits, frame)) :
        {T.finish(T.take(3n, Phase.with_run(world, input, before, _)), before) == before : E.Snapshot}
      prefix_snapshot(world, input, before, raw, context, bytes, N.cleaned(cleanup, N.removed(before, I.code(raw)), bytes, send))))

def receipt_query(~c: S.Configuration, +block: Engine.Block, +input: X.Reception, +primitives: Dispatch.Primitives,
  +raw: P.Request, +context: D.Context, +entry: G.Entry, +bytes: List<&2, U32>, +frames: List<&2, Q.Frame>,
  +source: {Engine.block_items(block) == Prelude.source(c, Engine.world(block), input, Chain.block_before(block), raw, Prelude.cleanup(primitives), Dispatch.send(primitives), frames) : List<&2, O.Item>},
  +authenticated: {D.authenticate(E.database(Chain.block_before(block)), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
  +empty: {String.eq(I.proof(raw), "") == True{} : Bool},
  +found: {G.lookup(E.instance(Chain.block_before(block)), I.code(raw), E.registry(Chain.block_before(block))) == Some{entry} : Maybe<&2, G.Entry>},
  +fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})) == True{} : Bool},
  +frame: {W.frame_receipt(W.InvalidatedReceipt{}) == Some{bytes} : Maybe<&2, List<&2, U32>>}) ->
  {B.query(O.Item, Engine.block_items(block), Prelude.phase_index(frames, 2n)) == Some{O.Item{Engine.world(block), E.database(Chain.block_before(block)), input, O.Invalidation{M.value(M.Receipt{}, raw, context, bytes)}}} : Maybe<&2, O.Item>}:
  Location.source_query(c, block, input, primitives, raw, frames, 2n, M.value(M.Receipt{}, raw, context, bytes), source,
    M.query(c, M.Receipt{}, Chain.block_before(block), raw, context, entry, bytes, Prelude.cleanup(primitives), Dispatch.send(primitives), authenticated, empty, found, fits, frame))

def replay(~c: S.Configuration, +block: Engine.Block, +input: X.Reception, +primitives: Dispatch.Primitives,
  +raw: P.Request, +context: D.Context, +entry: G.Entry, +bytes: List<&2, U32>, +frames: List<&2, Q.Frame>,
  +source: {Engine.block_items(block) == Prelude.source(c, Engine.world(block), input, Chain.block_before(block), raw, Prelude.cleanup(primitives), Dispatch.send(primitives), frames) : List<&2, O.Item>},
  +authenticated: {D.authenticate(E.database(Chain.block_before(block)), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
  +empty: {String.eq(I.proof(raw), "") == True{} : Bool},
  +found: {G.lookup(E.instance(Chain.block_before(block)), I.code(raw), E.registry(Chain.block_before(block))) == Some{entry} : Maybe<&2, G.Entry>},
  +fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})) == True{} : Bool},
  +frame: {W.frame_receipt(W.InvalidatedReceipt{}) == Some{bytes} : Maybe<&2, List<&2, U32>>}) ->
  {T.finish(T.take(Prelude.phase_index(frames, 2n), Engine.block_items(block)), Chain.block_before(block)) == Chain.block_before(block) : E.Snapshot}:
  Equal.trans(E.Snapshot, T.finish(T.take(Prelude.phase_index(frames, 2n), Engine.block_items(block)), Chain.block_before(block)),
    T.finish(T.take(Prelude.phase_index(frames, 2n), Prelude.source(c, Engine.world(block), input, Chain.block_before(block), raw, Prelude.cleanup(primitives), Dispatch.send(primitives), frames)), Chain.block_before(block)), Chain.block_before(block),
    Equal.cong(List<&2, O.Item>, E.Snapshot, items => T.finish(T.take(Prelude.phase_index(frames, 2n), items), Chain.block_before(block)), Engine.block_items(block),
      Prelude.source(c, Engine.world(block), input, Chain.block_before(block), raw, Prelude.cleanup(primitives), Dispatch.send(primitives), frames), source),
    actual_replay(c, Engine.world(block), input, Chain.block_before(block), raw, context, entry, bytes, frames, Prelude.cleanup(primitives), Dispatch.send(primitives), authenticated, empty, found, fits, frame))

def at_receipt(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String, +owner: Nat, +block: Engine.Block,
  +block_found: {B.query(Engine.Block, History.blocks(c, binding, public, script, seed, instance), owner) == Some{block} : Maybe<&2, Engine.Block>},
  +input: X.Reception, +primitives: Dispatch.Primitives,
  +raw: P.Request, +context: D.Context, +entry: G.Entry, +bytes: List<&2, U32>, +frames: List<&2, Q.Frame>,
  +source: {Engine.block_items(block) == Prelude.source(c, Engine.world(block), input, Chain.block_before(block), raw, Prelude.cleanup(primitives), Dispatch.send(primitives), frames) : List<&2, O.Item>},
  +authenticated: {D.authenticate(E.database(Chain.block_before(block)), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
  +empty: {String.eq(I.proof(raw), "") == True{} : Bool},
  +found: {G.lookup(E.instance(Chain.block_before(block)), I.code(raw), E.registry(Chain.block_before(block))) == Some{entry} : Maybe<&2, G.Entry>},
  +fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})) == True{} : Bool},
  +frame: {W.frame_receipt(W.InvalidatedReceipt{}) == Some{bytes} : Maybe<&2, List<&2, U32>>}) ->
  E.Current(History.environment(c, binding, public, script, seed, pi, artifacts, instance), Source.artifact(binding), I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), input}, O.time(History.position(c, binding, public, script, seed, instance, owner, Prelude.phase_index(frames, 2n))), Chain.block_before(block)):
  %replay(c, block, input, primitives, raw, context, entry, bytes, frames, source, authenticated, empty, found, fits, frame) :
    E.Current(History.environment(c, binding, public, script, seed, pi, artifacts, instance), Source.artifact(binding), I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), input}, O.time(History.position(c, binding, public, script, seed, instance, owner, Prelude.phase_index(frames, 2n))), _)
  Current.actual_serial_current_at_an_item_uses_its_exact_local_block_replay(c, binding, public, script, seed, pi, artifacts, instance,
    owner, block, History.position(c, binding, public, script, seed, instance, owner, Prelude.phase_index(frames, 2n)), Prelude.phase_index(frames, 2n), O.Item{Engine.world(block), E.database(Chain.block_before(block)), input, O.Invalidation{M.value(M.Receipt{}, raw, context, bytes)}},
    Items.an_actual_retained_block_local_item_query_recovers_the_same_engine_global_item(c, binding, public, script, 0n, History.boot(seed, instance), owner, block, Prelude.phase_index(frames, 2n), O.Item{Engine.world(block), E.database(Chain.block_before(block)), input, O.Invalidation{M.value(M.Receipt{}, raw, context, bytes)}}, block_found,
      receipt_query(c, block, input, primitives, raw, context, entry, bytes, frames, source, authenticated, empty, found, fits, frame)),
    block_found, receipt_query(c, block, input, primitives, raw, context, entry, bytes, frames, source, authenticated, empty, found, fits, frame), {==})
