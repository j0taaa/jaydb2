# Exact snapshot/time normalization after the actual registration and before
# conclusion. The full Current witness is obtained from the existing history
# extraction theorem; only DATA equalities normalize its indices here.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Interface.bend as I
import ../../../contract/Logic.bend as L
import ../../../contract/PreparedLaws.bend as H
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/PreparedRegistry.bend as G
import ../../../contract/Protocol.bend as P
import ../../../contract/Requirements.bend as R
import ../../../contract/Resources.bend as X
import ../../../contract/Semantics.bend as S
import ../../SourceService.bend as Source
import ../specification/ServiceLaws.bend as E
import ../phases/PreparePhases.bend as V
import ../phases/PrepareEvents.bend as Events
import ../model/EventObserver.bend as O
import ../model/EventHistory.bend as T
import ../model/PreparationCurrent.bend as A
import ../model/PreparationPrefix.bend as Prefix
import ../model/FrameBounds.bend as B
import ./PreparationMilestones.bend as M

def after(+before: E.Snapshot, entry: G.Entry) -> E.Snapshot:
  V.registered_snapshot(before, Events.registered(before, entry))

def Properties(-items: List<&2, O.Item>, +before: E.Snapshot, +entry: G.Entry) -> Type:
  L.E<{T.finish(T.take(8n, items), before) == after(before, entry) : E.Snapshot},
    {B.count(O.Item, T.take(8n, items)) == 8n : Nat}>

def known_properties(+world: Nat, +input: X.Reception, +mode: V.Mode, +raw: P.Request, +context: D.Context,
  +before: E.Snapshot, +entry: G.Entry, +bytes: List<&2, U32>, send: V.SendReturn) ->
  Properties(A.with_run(world, input, before, Events.success(mode, raw, context, before, entry, bytes, send)), before, entry):
  match send:
    case V.SendPending{}: L.Both{{==}, {==}}
    case V.SendComplete{}: L.Both{{==}, {==}}
    case V.SendInterrupted{prefix}: L.Both{{==}, {==}}

def actual_properties(~c: S.Configuration, +world: Nat, +input: X.Reception, +mode: V.Mode, +raw: P.Request, +context: D.Context,
  +before: E.Snapshot, +handle: String, +seal: String, +bytes: List<&2, U32>, +send: V.SendReturn,
  authenticated: {D.authenticate(E.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
  fresh: {G.lookup(E.instance(before), handle, E.registry(before)) == None{} : Maybe<&2, G.Entry>},
  fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})) == True{} : Bool},
  frame: {W.frame_receipt(W.PreparedReceipt{handle}) == Some{bytes} : Maybe<&2, List<&2, U32>>}) ->
  Properties(A.source(c, world, input, before, mode, raw,
    V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send}),
    before, V.entry(mode, raw, E.instance(before), handle, seal)):
  %Equal.sym(V.PreparationRun,
    V.run(c, mode, raw, before, V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send}),
    Events.success(mode, raw, context, before, V.entry(mode, raw, E.instance(before), handle, seal), bytes, send),
    Events.successful_preparation_has_the_exact_dispatcher_phases(c, mode, raw, before, context, handle, seal, bytes, send,
      authenticated, fresh, fits, frame)) :
    Properties(A.with_run(world, input, before, _), before, V.entry(mode, raw, E.instance(before), handle, seal))
  known_properties(world, input, mode, raw, context, before, V.entry(mode, raw, E.instance(before), handle, seal), bytes, send)

def normalize_current(~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~c: S.Configuration,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  ~world: Nat, ~input: X.Reception, ~mode: V.Mode, ~raw: P.Request, ~handle: String, ~seal: String, ~send: V.SendReturn,
  properties: Properties(A.source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw,
      V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send}),
    E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, V.entry(mode, raw, instance, handle, seal)),
  current: Prefix.CurrentAtSnapshot(M.environment(binding, public, c, seed, pi, artifacts, instance, world, input, mode, raw, handle, seal, send),
    c, Source.artifact(binding), world, input,
    B.count(O.Item, T.take(8n, A.source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw,
      V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send}))),
    T.finish(T.take(8n, A.source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw,
      V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send})), E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}))) ->
  Prefix.CurrentAtSnapshot(M.environment(binding, public, c, seed, pi, artifacts, instance, world, input, mode, raw, handle, seal, send),
    c, Source.artifact(binding), world, input, 8n,
    after(E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, V.entry(mode, raw, instance, handle, seal))):
  match properties:
    case L.Both{same_snapshot, same_count}:
      %same_snapshot : Prefix.CurrentAtSnapshot(M.environment(binding, public, c, seed, pi, artifacts, instance, world, input, mode, raw, handle, seal, send),
        c, Source.artifact(binding), world, input, 8n, _)
      %same_count : Prefix.CurrentAtSnapshot(M.environment(binding, public, c, seed, pi, artifacts, instance, world, input, mode, raw, handle, seal, send),
        c, Source.artifact(binding), world, input, _,
        T.finish(T.take(8n, A.source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw,
          V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send})), E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}))
      current

law actual_registration_derives_the_exact_complete_current_snapshot_at_conclusion:
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~c: S.Configuration
  for ~seed: Unit -> D.State
  for ~pi: String
  for ~artifacts: H.Artifacts
  for ~instance: String
  for ~world: Nat
  for ~input: X.Reception
  for ~mode: V.Mode
  for ~raw: P.Request
  for ~context: D.Context
  for ~handle: String
  for ~seal: String
  for ~bytes: List<&2, U32>
  for ~send: V.SendReturn
  for +authenticated: {D.authenticate(seed(Unit{}), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>}
  for +fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})) == True{} : Bool}
  for +frame: {W.frame_receipt(W.PreparedReceipt{handle}) == Some{bytes} : Maybe<&2, List<&2, U32>>}
  Prefix.CurrentAtSnapshot(M.environment(binding, public, c, seed, pi, artifacts, instance, world, input, mode, raw, handle, seal, send),
    c, Source.artifact(binding), world, input, 8n,
    after(E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, V.entry(mode, raw, instance, handle, seal)))
def actual_registration_derives_the_exact_complete_current_snapshot_at_conclusion(binding, public, c, seed, pi, artifacts,
  instance, world, input, mode, raw, context, handle, seal, bytes, send, authenticated, fits, frame):
  normalize_current(binding, public, c, seed, pi, artifacts, instance, world, input, mode, raw, handle, seal, send,
    actual_properties(c, world, input, mode, raw, context, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, handle, seal, bytes, send,
      authenticated, {==}, fits, frame),
    A.actual_preparation_mutation_has_full_current_history_before_its_conclusion(binding, public, c, seed, pi, artifacts,
      instance, world, input, mode, raw, context, handle, seal, bytes, send, authenticated, fits, frame))
