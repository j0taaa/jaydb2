# Real authorization at ReceiptPrepared phase TWO, before actual removal.
# Only physical reception is a native boundary; current/auth/lookup are derived.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/PreparedLaws.bend as H
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/PreparedRegistry.bend as G
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Requirements.bend as R
import ../../../../../contract/Resources.bend as X
import ../../../../../contract/Semantics.bend as S
import ../../../../ProtocolService.bend as Q
import ../../../../SourceService.bend as Source
import ../../../../Orders.bend as Order
import ../../../../PreparedInvalidationDispatch.bend as Ready
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../phases/InvalidationPhases.bend as N
import ../../../model/EventObserver.bend as O
import ../../../model/FrameBounds.bend as B
import ../../../model/serial/Engine.bend as Engine
import ../../../model/serial/Chain.bend as Chain
import ../../../model/serial/Dispatch.bend as Dispatch
import ../header/History.bend as History
import ../observed-invalidation/Prelude.bend as Prelude
import ../observed-invalidation/Before.bend as Before
import ./InvalidationMilestones.bend as M
import ./InvalidationCurrent.bend as Current

def actual(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  +owner: Nat, +block: Engine.Block, +input: X.Reception, +primitives: Dispatch.Primitives, +raw: P.Request, +context: D.Context, +entry: G.Entry, +bytes: List<&2, U32>, +frames: List<&2, Q.Frame>,
  +known: {B.query(Engine.Block, History.blocks(c, binding, public, script, seed, instance), owner) == Some{block} : Maybe<&2, Engine.Block>},
  +source: {Engine.block_items(block) == Prelude.source(c, Engine.world(block), input, Chain.block_before(block), raw, Prelude.cleanup(primitives), Dispatch.send(primitives), frames) : List<&2, O.Item>},
  +auth: {D.authenticate(E.database(Chain.block_before(block)), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
  +empty: {String.eq(I.proof(raw), "") == True{} : Bool},
  +lookup: {G.lookup(E.instance(Chain.block_before(block)), I.code(raw), E.registry(Chain.block_before(block))) == Some{entry} : Maybe<&2, G.Entry>},
  +fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})) == True{} : Bool},
  +frame: {W.frame_receipt(W.InvalidatedReceipt{}) == Some{bytes} : Maybe<&2, List<&2, U32>>},
  received: W.Received(c, input, W.Extension{W.Invalidate{}, raw})) ->
  E.ReceiptAuthorization(History.environment(c, binding, public, script, seed, pi, artifacts, instance), Source.artifact(binding), I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), input},
    O.time(History.position(c, binding, public, script, seed, instance, owner, Prelude.phase_index(frames, 2n))), W.InvalidatedReceipt{}):
  (Chain.block_before(block), raw, entry, context,
    L.Both{Current.at_receipt(c, binding, public, script, seed, pi, artifacts, instance, owner, block, known, input, primitives, raw, context, entry, bytes, frames, source, auth, empty, lookup, fits, frame),
      L.Both{{==}, L.Both{Before.phase_before(c, binding, public, script, seed, pi, artifacts, instance, owner, block, input, primitives, raw, frames, 1n, 2n,
          N.InvalidationBase{V.IdentityEstablished{W.Extension{W.Invalidate{}, raw}, Some{context}}}, known, source,
          M.query(c, M.Identity{}, Chain.block_before(block), raw, context, entry, bytes, Prelude.cleanup(primitives), Dispatch.send(primitives), auth, empty, lookup, fits, frame), {==}),
        Ready.current_invalidation_ready(c, E.database(Chain.block_before(block)), input, E.instance(Chain.block_before(block)), E.registry(Chain.block_before(block)), raw, entry, context, received, auth, Order.string_equal(I.proof(raw), "", empty), lookup)}}})
