# Exact named milestones of the ACTUAL successful dispatcher. Queries are
# derived from the full run equality; later send returns do not erase prefixes.
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
import ../model/PreparationCurrent.bend as A
import ../model/PreparationPrefix.bend as Prefix
import ../model/FrameBounds.bend as B
import ./PreparationAcceptance.bend as Acceptance

type Milestone is Data:
  AcceptancePoint{}
  HandlePoint{}
  ReceiptPoint{}
  SealPoint{}
  RegistrationPoint{}
  ConclusionPoint{}

def index(point: Milestone) -> Nat:
  match point:
    case AcceptancePoint{}: 2n
    case HandlePoint{}: 3n
    case ReceiptPoint{}: 4n
    case SealPoint{}: 5n
    case RegistrationPoint{}: 6n
    case ConclusionPoint{}: 7n

def value(point: Milestone, mode: V.Mode, raw: P.Request, context: D.Context,
  +before: E.Snapshot, +entry: G.Entry, bytes: List<&2, U32>) -> V.PreparationEvent:
  match point:
    case AcceptancePoint{}: V.Accepted{W.Extension{V.operation(mode), raw}, context}
    case HandlePoint{}: V.HandleChosen{G.handle(entry)}
    case ReceiptPoint{}: V.ReceiptPrepared{W.PreparedReceipt{G.handle(entry)}, bytes}
    case SealPoint{}: V.ArtifactSealed{entry}
    case RegistrationPoint{}: V.RegistryChanged{entry, before, V.registered_snapshot(before, Events.registered(before, entry))}
    case ConclusionPoint{}: V.ReceiptConcluded{W.PreparedReceipt{G.handle(entry)}, Events.registered(before, entry),
      V.registered_snapshot(before, Events.registered(before, entry)), False{}}

def known_query(point: Milestone, +mode: V.Mode, +raw: P.Request, +context: D.Context,
  +before: E.Snapshot, +entry: G.Entry, +bytes: List<&2, U32>, send: V.SendReturn) ->
  {B.query(V.PreparationEvent, V.events(Events.success(mode, raw, context, before, entry, bytes, send)), index(point)) ==
    Some{value(point, mode, raw, context, before, entry, bytes)} : Maybe<&2, V.PreparationEvent>}:
  match point send:
    case AcceptancePoint{} V.SendPending{}: {==}
    case AcceptancePoint{} V.SendComplete{}: {==}
    case AcceptancePoint{} V.SendInterrupted{prefix}: {==}
    case HandlePoint{} V.SendPending{}: {==}
    case HandlePoint{} V.SendComplete{}: {==}
    case HandlePoint{} V.SendInterrupted{prefix}: {==}
    case ReceiptPoint{} V.SendPending{}: {==}
    case ReceiptPoint{} V.SendComplete{}: {==}
    case ReceiptPoint{} V.SendInterrupted{prefix}: {==}
    case SealPoint{} V.SendPending{}: {==}
    case SealPoint{} V.SendComplete{}: {==}
    case SealPoint{} V.SendInterrupted{prefix}: {==}
    case RegistrationPoint{} V.SendPending{}: {==}
    case RegistrationPoint{} V.SendComplete{}: {==}
    case RegistrationPoint{} V.SendInterrupted{prefix}: {==}
    case ConclusionPoint{} V.SendPending{}: {==}
    case ConclusionPoint{} V.SendComplete{}: {==}
    case ConclusionPoint{} V.SendInterrupted{prefix}: {==}

law actual_successful_preparation_has_every_exact_milestone_query:
  for ~c: S.Configuration
  for +point: Milestone
  for +mode: V.Mode
  for +raw: P.Request
  for +before: E.Snapshot
  for +context: D.Context
  for +handle: String
  for +seal: String
  for +bytes: List<&2, U32>
  for +send: V.SendReturn
  for authenticated: {D.authenticate(E.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>}
  for fresh: {G.lookup(E.instance(before), handle, E.registry(before)) == None{} : Maybe<&2, G.Entry>}
  for fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})) == True{} : Bool}
  for frame: {W.frame_receipt(W.PreparedReceipt{handle}) == Some{bytes} : Maybe<&2, List<&2, U32>>}
  {B.query(V.PreparationEvent, V.events(V.run(c, mode, raw, before,
      V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send})), index(point)) ==
    Some{value(point, mode, raw, context, before, V.entry(mode, raw, E.instance(before), handle, seal), bytes)} : Maybe<&2, V.PreparationEvent>}
def actual_successful_preparation_has_every_exact_milestone_query(c, point, mode, raw, before, context, handle, seal, bytes,
  send, authenticated, fresh, fits, frame):
  Equal.trans(Maybe<&2, V.PreparationEvent>,
    B.query(V.PreparationEvent, V.events(V.run(c, mode, raw, before,
      V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send})), index(point)),
    B.query(V.PreparationEvent, V.events(Events.success(mode, raw, context, before,
      V.entry(mode, raw, E.instance(before), handle, seal), bytes, send)), index(point)),
    Some{value(point, mode, raw, context, before, V.entry(mode, raw, E.instance(before), handle, seal), bytes)},
    Equal.cong(V.PreparationRun, Maybe<&2, V.PreparationEvent>, run => B.query(V.PreparationEvent, V.events(run), index(point)),
      V.run(c, mode, raw, before, V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send}),
      Events.success(mode, raw, context, before, V.entry(mode, raw, E.instance(before), handle, seal), bytes, send),
      Events.successful_preparation_has_the_exact_dispatcher_phases(c, mode, raw, before, context, handle, seal, bytes, send,
        authenticated, fresh, fits, frame)),
    known_query(point, mode, raw, context, before, V.entry(mode, raw, E.instance(before), handle, seal), bytes, send))

def environment(~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~c: S.Configuration,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  ~world: Nat, ~input: X.Reception, ~mode: V.Mode, ~raw: P.Request, ~handle: String, ~seal: String, ~send: V.SendReturn) -> E.Environment:
  Acceptance.environment(binding, public, c, seed, pi, artifacts, instance, world, input, mode, raw,
    V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send})

def actual_observation(~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~c: S.Configuration,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  ~world: Nat, ~input: X.Reception, ~mode: V.Mode, ~raw: P.Request, ~context: D.Context,
  ~handle: String, ~seal: String, ~bytes: List<&2, U32>, ~send: V.SendReturn, ~point: Milestone,
  authenticated: {D.authenticate(seed(Unit{}), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
  fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})) == True{} : Bool},
  frame: {W.frame_receipt(W.PreparedReceipt{handle}) == Some{bytes} : Maybe<&2, List<&2, U32>>}) ->
  E.observes(environment(binding, public, c, seed, pi, artifacts, instance, world, input, mode, raw, handle, seal, send),
    Source.artifact(binding), I.Serve{world, c, seed(Unit{}), input}, O.time(Succ{index(point)}),
    V.fact(c, binding, public, value(point, mode, raw, context, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}},
      V.entry(mode, raw, instance, handle, seal), bytes))):
  Prefix.a_real_query_constructs_the_exact_full_observation(binding, public, c, seed, pi, artifacts,
    A.source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw,
      V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send}), instance,
    Succ{index(point)}, O.Item{world, seed(Unit{}), input,
      O.Preparation{value(point, mode, raw, context, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}},
        V.entry(mode, raw, instance, handle, seal), bytes)}},
    Prefix.exact_dispatcher_phase_query_supplies_the_actual_observer_query(c, world, input,
      E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw,
      V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send}, index(point),
      value(point, mode, raw, context, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, V.entry(mode, raw, instance, handle, seal), bytes),
      actual_successful_preparation_has_every_exact_milestone_query(c, point, mode, raw,
        E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, context, handle, seal, bytes, send, authenticated, {==}, fits, frame)))

def actual_before(~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~c: S.Configuration,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  ~world: Nat, ~input: X.Reception, ~mode: V.Mode, ~raw: P.Request, ~context: D.Context,
  ~handle: String, ~seal: String, ~bytes: List<&2, U32>, ~send: V.SendReturn, ~point: Milestone, -at: Nat,
  authenticated: {D.authenticate(seed(Unit{}), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
  fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})) == True{} : Bool},
  frame: {W.frame_receipt(W.PreparedReceipt{handle}) == Some{bytes} : Maybe<&2, List<&2, U32>>},
  earlier: {Nat.is_lt(O.time(Succ{index(point)}), at) == True{} : Bool}) ->
  E.Before(environment(binding, public, c, seed, pi, artifacts, instance, world, input, mode, raw, handle, seal, send),
    Source.artifact(binding), I.Serve{world, c, seed(Unit{}), input}, at,
    V.fact(c, binding, public, value(point, mode, raw, context, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}},
      V.entry(mode, raw, instance, handle, seal), bytes))):
  (O.time(Succ{index(point)}), L.Both{earlier,
    actual_observation(binding, public, c, seed, pi, artifacts, instance, world, input, mode, raw, context,
      handle, seal, bytes, send, point, authenticated, fits, frame)})
