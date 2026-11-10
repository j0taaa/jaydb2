# Exact earlier acceptance + handle selection authorize the framed receipt.
# This internal adapter receives locally DERIVED queries, not semantic validity.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/PreparedLaws.bend as H
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Resources.bend as X
import ../../../../../contract/Semantics.bend as S
import ../../../../ProtocolService.bend as Q
import ../../../../SourceService.bend as Source
import ../../../../HostTransitions.bend as Host
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../model/EventObserver.bend as O
import ../../../model/FrameBounds.bend as B
import ../../../model/serial/Engine.bend as Engine
import ../../../model/serial/Chain.bend as Chain
import ../../../model/serial/Dispatch.bend as Dispatch
import ../../../model/serial/PreparationPrelude.bend as Prelude
import ../header/History.bend as History
import ../header/PhaseBefore.bend as Before
import ./PreparationSite.bend as Site

def actual(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~script: List<&2, Engine.Job>,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  +owner: Nat, +block: Engine.Block, +input: X.Reception, +primitives: Dispatch.Primitives, +mode: V.Mode, +raw: P.Request, +frames: List<&2, Q.Frame>, +receipt: W.Receipt, +index: Nat,
  +known: {B.query(Engine.Block, History.blocks(c, binding, public, script, seed, instance), owner) == Some{block} : Maybe<&2, Engine.Block>},
  +source: {Engine.block_items(block) == Prelude.source(c, Engine.world(block), input, Chain.block_before(block), mode, raw, Prelude.returns(primitives), frames) : List<&2, O.Item>},
  site: Site.Site<mode, raw, V.events(V.run(c, mode, raw, Chain.block_before(block), Prelude.returns(primitives))), index, receipt>) ->
  E.ReceiptAuthorization(History.environment(c, binding, public, script, seed, pi, artifacts, instance), Source.artifact(binding), I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), input},
    O.time(History.position(c, binding, public, script, seed, instance, owner, Prelude.phase_index(frames, index))), receipt):
  match site:
    case Site.Site{+context, +handle, payload, position, accepted, chosen}:
      %Equal.sym(W.Receipt, receipt, W.PreparedReceipt{handle}, payload) : E.ReceiptAuthorization(History.environment(c, binding, public, script, seed, pi, artifacts, instance), Source.artifact(binding), I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), input}, O.time(History.position(c, binding, public, script, seed, instance, owner, Prelude.phase_index(frames, index))), _)
      %Equal.sym(Nat, index, 4n, position) : E.ReceiptAuthorization(History.environment(c, binding, public, script, seed, pi, artifacts, instance), Source.artifact(binding), I.Serve{Engine.world(block), c, E.database(Chain.block_before(block)), input}, O.time(History.position(c, binding, public, script, seed, instance, owner, Prelude.phase_index(frames, _))), W.PreparedReceipt{handle})
      (W.Extension{V.operation(mode), raw}, context, Source.program(binding, Host.origin(public, I.code(raw))),
        L.Both{Before.phase_before(c, binding, public, script, seed, pi, artifacts, instance, owner, block, input, primitives, mode, raw, frames, 2n, 4n, V.Accepted{W.Extension{V.operation(mode), raw}, context}, known, source, accepted, {==}),
          Before.phase_before(c, binding, public, script, seed, pi, artifacts, instance, owner, block, input, primitives, mode, raw, frames, 3n, 4n, V.HandleChosen{handle}, known, source, chosen, {==})})
