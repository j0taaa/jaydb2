# Codec insertion preserves exact replay, including AFTER real registry
# mutation. Unlike unchanged-prefix properties, no before==after is assumed.
# Final clauses use this only with the actual decoded source, never to hide
# arbitrary native effects or publication cofacts.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Interface.bend as I
import ../../../../contract/Logic.bend as L
import ../../../../contract/PreparedProtocol.bend as W
import ../../../../contract/PreparedRegistry.bend as G
import ../../../../contract/Protocol.bend as P
import ../../../../contract/Requirements.bend as R
import ../../../../contract/Resources.bend as X
import ../../../../contract/Semantics.bend as S
import ../../../ProtocolService.bend as Q
import ../../specification/ServiceLaws.bend as E
import ../../phases/PreparePhases.bend as V
import ../../model/EventObserver.bend as O
import ../../model/EventHistory.bend as T
import ../../model/FrameBounds.bend as B
import ../../model/PreparationCurrent.bend as Phase
import ../../model/serial/PreparationPrelude.bend as Prelude
import ../PreparationAfterState.bend as State

def through_codec(+frames: List<&2, Q.Frame>, +world: Nat, +input: X.Reception, +before: E.Snapshot,
  +raw: P.Request, +tail: List<&2, O.Item>, +count: Nat) ->
  {T.finish(T.take(Nat.add(B.count(Q.Frame, frames), count),
    T.append(Prelude.codec_items(world, input, E.database(before), raw, frames), tail)), before) ==
    T.finish(T.take(count, tail), before) : E.Snapshot}:
  match frames:
    case Nil{}: {==}
    case Con{frame, +rest}: through_codec(rest, world, input, before, raw, tail, count)

law measured_codec_insertion_preserves_every_exact_preparation_prefix_snapshot:
  for +world: Nat
  for +input: X.Reception
  for +before: E.Snapshot
  for +raw: P.Request
  for +frames: List<&2, Q.Frame>
  for +run: V.PreparationRun
  for +count: Nat
  {T.finish(T.take(Prelude.phase_index(frames, count), Prelude.with_run(world, input, before, raw, frames, run)), before) ==
    T.finish(T.take(Succ{count}, Phase.with_run(world, input, before, run)), before) : E.Snapshot}
def measured_codec_insertion_preserves_every_exact_preparation_prefix_snapshot(world, input, before, raw, frames, run, count):
  match run:
    case V.PreparationRun{events, result, snapshot, waiting, closed}:
      through_codec(frames, world, input, before, raw, Phase.phase_items(world, E.database(before), input, events), count)


def after_registration(-items: List<&2, O.Item>, +before: E.Snapshot, +entry: G.Entry,
  properties: State.Properties(items, before, entry)) ->
  {T.finish(T.take(8n, items), before) == State.after(before, entry) : E.Snapshot}:
  match properties:
    case L.Both{snapshot, measured}: snapshot

law actual_registered_preparation_replays_to_the_exact_inserted_snapshot_after_its_real_codec_prefix:
  for ~c: S.Configuration
  for +world: Nat
  for +input: X.Reception
  for +before: E.Snapshot
  for +mode: V.Mode
  for +raw: P.Request
  for +context: D.Context
  for +handle: String
  for +seal: String
  for +bytes: List<&2, U32>
  for +frames: List<&2, Q.Frame>
  for +send: V.SendReturn
  for authenticated: {D.authenticate(E.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>}
  for fresh: {G.lookup(E.instance(before), handle, E.registry(before)) == None{} : Maybe<&2, G.Entry>}
  for fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})) == True{} : Bool}
  for frame: {W.frame_receipt(W.PreparedReceipt{handle}) == Some{bytes} : Maybe<&2, List<&2, U32>>}
  {T.finish(T.take(Prelude.phase_index(frames, 7n),
    Prelude.source(c, world, input, before, mode, raw, V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send}, frames)), before) ==
    State.after(before, V.entry(mode, raw, E.instance(before), handle, seal)) : E.Snapshot}
def actual_registered_preparation_replays_to_the_exact_inserted_snapshot_after_its_real_codec_prefix(c, world, input, before, mode, raw, context, handle, seal, bytes, frames, send, authenticated, fresh, fits, frame):
  Equal.trans(E.Snapshot,
    T.finish(T.take(Prelude.phase_index(frames, 7n), Prelude.source(c, world, input, before, mode, raw,
      V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send}, frames)), before),
    T.finish(T.take(8n, Phase.source(c, world, input, before, mode, raw,
      V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send})), before),
    State.after(before, V.entry(mode, raw, E.instance(before), handle, seal)),
    measured_codec_insertion_preserves_every_exact_preparation_prefix_snapshot(world, input, before, raw, frames,
      V.run(c, mode, raw, before, V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send}), 7n),
    after_registration(Phase.source(c, world, input, before, mode, raw,
      V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send}), before,
      V.entry(mode, raw, E.instance(before), handle, seal),
      State.actual_properties(c, world, input, mode, raw, context, before, handle, seal, bytes, send, authenticated, fresh, fits, frame)))
