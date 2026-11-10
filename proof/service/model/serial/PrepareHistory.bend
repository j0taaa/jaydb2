# Full actual preparation event replay, including every error/pending prefix.
# No validity, certification, completed result or target Current is an input.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Interface.bend as I
import ../../../../contract/Logic.bend as L
import ../../../../contract/PreparedLaws.bend as H
import ../../../../contract/PreparedProtocol.bend as W
import ../../../../contract/PreparedRegistry.bend as G
import ../../../../contract/Protocol.bend as P
import ../../../../contract/Requirements.bend as R
import ../../../../contract/Resources.bend as X
import ../../../../contract/Semantics.bend as S
import ../../specification/ServiceLaws.bend as E
import ../../phases/PreparePhases.bend as V
import ../EventObserver.bend as O
import ./Common.bend as C
import ./LocalHistory.bend as J


def Sound(+position: J.Position, +run: V.PreparationRun, before: E.Snapshot) -> Type:
  J.Sound(position, C.prepare_events(V.events(run)), before, V.snapshot(run))


def push(+position: J.Position, +event: V.PreparationEvent, +run: V.PreparationRun, +before: E.Snapshot,
  quiet: {O.phase_change(event) == None{} : Maybe<&2, O.Change>},
  later: Sound(position, run, before)) -> Sound(position, V.push(event, run), before):
  V.PreparationRun{events, result, snapshot, waiting, closed} = run
  J.quiet_push(position, O.Preparation{event}, C.prepare_events(events), before, snapshot, quiet, later)


def delivery(+position: J.Position, +send: V.SendReturn, +bytes: List<&2, U32>, completed: H.ControlResult, +before: E.Snapshot) ->
  Sound(position, V.delivery(send, bytes, completed, before), before):
  match send:
    case V.SendPending{}: J.no_events(position, before)
    case V.SendComplete{}: J.quiet_all(position, [O.Preparation{V.Delivered{bytes}}], before, L.Both{{==}, Unit{}})
    case V.SendInterrupted{prefix}:
      J.quiet_all(position, [O.Preparation{V.Interrupted{prefix}}, O.Preparation{V.Closed{}}], before, L.Both{{==}, L.Both{{==}, Unit{}}})


def error_framed(+position: J.Position, +status: S.Status, +before: E.Snapshot, +send: V.SendReturn, +frame: Maybe<&2, List<&2, U32>>) ->
  Sound(position, V.error_framed(status, before, send, frame), before):
  match frame:
    case None{}: J.no_events(position, before)
    case Some{+bytes}:
      push(position, V.ErrorPrepared{status, bytes},
        V.push(V.ErrorConcluded{status, before, False{}}, V.delivery(send, bytes, H.ControlResult{E.database(before), E.registry(before), H.Error{status}}, before)), before, {==},
        push(position, V.ErrorConcluded{status, before, False{}}, V.delivery(send, bytes, H.ControlResult{E.database(before), E.registry(before), H.Error{status}}, before), before, {==},
          delivery(position, send, bytes, H.ControlResult{E.database(before), E.registry(before), H.Error{status}}, before)))


def error(+position: J.Position, +status: S.Status, +before: E.Snapshot, +send: V.SendReturn) -> Sound(position, V.error(status, before, send), before):
  error_framed(position, status, before, send, P.frame(S.response_value(S.response_error(status))))


def failed(+position: J.Position, +stage: X.Stage, +identifier: String, fatal: Bool, +before: E.Snapshot, +send: V.SendReturn) ->
  Sound(position, V.failed(stage, identifier, fatal, before, send), before):
  match fatal:
    case True{}:
      J.quiet_all(position, [O.Preparation{V.PrimitiveFailed{stage, identifier, True{}}}, O.Preparation{V.Closed{}}], before, L.Both{{==}, L.Both{{==}, Unit{}}})
    case False{}:
      push(position, V.PrimitiveFailed{stage, identifier, False{}}, V.error(S.Failure{}, before, send), before, {==}, error(position, S.Failure{}, before, send))


def registered_tail(+position: J.Position, +before: E.Snapshot, +entry: G.Entry, +run: V.PreparationRun, +after: E.Snapshot,
  scope: {E.instance(before) == E.instance(after) : String},
  selection: {J.selected(position) == E.database(before) : D.State},
  later: Sound(position, run, after)) -> Sound(position, V.push(V.RegistryChanged{entry, before, after}, run), before):
  V.PreparationRun{events, result, snapshot, waiting, closed} = run
  J.mutation_push(position, O.Preparation{V.RegistryChanged{entry, before, after}}, C.prepare_events(events), True{}, E.Register{entry}, before, after, snapshot,
    {==}, scope, selection, later)


def register_result(+position: J.Position, +completed: H.ControlResult, +before: E.Snapshot, +entry: G.Entry, +bytes: List<&2, U32>, +send: V.SendReturn,
  selection: {J.selected(position) == E.database(before) : D.State}) -> Sound(position, V.register_result(completed, before, entry, bytes, send), before):
  match completed:
    case H.ControlResult{state, entries, H.Error{status}}: error(position, status, before, send)
    case H.ControlResult{state, entries, H.Metadata{+receipt}}:
      +actual: H.ControlResult = H.ControlResult{state, entries, H.Metadata{receipt}}
      +after = V.registered_snapshot(before, actual)
      registered_tail(position, before, entry,
        V.push(V.ReceiptConcluded{receipt, actual, after, False{}}, V.delivery(send, bytes, actual, after)), after, {==}, selection,
        push(position, V.ReceiptConcluded{receipt, actual, after, False{}}, V.delivery(send, bytes, actual, after), after, {==}, delivery(position, send, bytes, actual, after)))


def seal_result(~c: S.Configuration, +position: J.Position, +seal: V.SealReturn, +mode: V.Mode, +raw: P.Request,
  +before: E.Snapshot, +handle: String, +bytes: List<&2, U32>, +send: V.SendReturn,
  selection: {J.selected(position) == E.database(before) : D.State}) -> Sound(position, V.seal_result(c, seal, mode, raw, before, handle, bytes, send), before):
  match seal:
    case V.SealPending{}: J.no_events(position, before)
    case V.SealFailed{stage, identifier, fatal}: failed(position, stage, identifier, fatal, before, send)
    case V.SealSucceeded{seal}:
      +entry = V.entry(mode, raw, E.instance(before), handle, seal)
      push(position, V.ArtifactSealed{entry}, V.register_result(H.register(c, E.database(before), E.instance(before), entry, E.registry(before)), before, entry, bytes, send), before, {==},
        register_result(position, H.register(c, E.database(before), E.instance(before), entry, E.registry(before)), before, entry, bytes, send, selection))


def fitting_frame(~c: S.Configuration, +position: J.Position, +frame: Maybe<&2, List<&2, U32>>, +mode: V.Mode, +raw: P.Request,
  +before: E.Snapshot, +handle: String, +seal: V.SealReturn, +send: V.SendReturn,
  selection: {J.selected(position) == E.database(before) : D.State}) -> Sound(position, V.fitting_frame(c, frame, mode, raw, before, handle, seal, send), before):
  match frame:
    case None{}: J.no_events(position, before)
    case Some{+bytes}:
      push(position, V.ReceiptPrepared{W.PreparedReceipt{handle}, bytes}, V.seal_result(c, seal, mode, raw, before, handle, bytes, send), before, {==},
        seal_result(c, position, seal, mode, raw, before, handle, bytes, send, selection))


def receipt_fit(~c: S.Configuration, +position: J.Position, fits: Bool, +mode: V.Mode, +raw: P.Request,
  +before: E.Snapshot, +handle: String, +seal: V.SealReturn, +send: V.SendReturn,
  selection: {J.selected(position) == E.database(before) : D.State}) -> Sound(position, V.receipt_fit(c, fits, mode, raw, before, handle, seal, send), before):
  match fits:
    case False{}: error(position, S.Limit{}, before, send)
    case True{}: fitting_frame(c, position, W.frame_receipt(W.PreparedReceipt{handle}), mode, raw, before, handle, seal, send, selection)


def allocated(~c: S.Configuration, +position: J.Position, +allocation: V.AllocatorReturn, +mode: V.Mode, +raw: P.Request,
  +before: E.Snapshot, +seal: V.SealReturn, +send: V.SendReturn,
  selection: {J.selected(position) == E.database(before) : D.State}) -> Sound(position, V.allocated(c, allocation, mode, raw, before, seal, send), before):
  match allocation:
    case V.AllocatorPending{}: J.no_events(position, before)
    case V.AllocatorFailed{stage, identifier, fatal}: failed(position, stage, identifier, fatal, before, send)
    case V.AllocatorChosen{+handle}:
      push(position, V.HandleChosen{handle}, V.receipt_fit(c, R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})), mode, raw, before, handle, seal, send), before, {==},
        receipt_fit(c, position, R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})), mode, raw, before, handle, seal, send, selection))


def checked(~c: S.Configuration, +position: J.Position, +check: V.CheckerReturn, +mode: V.Mode, +raw: P.Request,
  +context: D.Context, +before: E.Snapshot, +allocation: V.AllocatorReturn, +seal: V.SealReturn, +send: V.SendReturn,
  selection: {J.selected(position) == E.database(before) : D.State}) -> Sound(position, V.checked(c, check, mode, raw, context, before, allocation, seal, send), before):
  match check:
    case V.CheckerPending{}: J.no_events(position, before)
    case V.CheckerFailed{stage, identifier, fatal}: failed(position, stage, identifier, fatal, before, send)
    case V.CheckerRefuted{}:
      push(position, V.Refuted{W.Extension{V.operation(mode), raw}, context}, V.error(S.Certificate{}, before, send), before, {==}, error(position, S.Certificate{}, before, send))
    case V.CheckerAccepted{}:
      push(position, V.Accepted{W.Extension{V.operation(mode), raw}, context}, V.allocated(c, allocation, mode, raw, before, seal, send), before, {==},
        allocated(c, position, allocation, mode, raw, before, seal, send, selection))


def authenticated(~c: S.Configuration, +position: J.Position, +identity: Maybe<&2, D.Context>, +mode: V.Mode, +raw: P.Request,
  +before: E.Snapshot, +returns: V.Returns,
  selection: {J.selected(position) == E.database(before) : D.State}) -> Sound(position, V.authenticated(c, identity, mode, raw, before, returns), before):
  match identity:
    case None{}: error(position, S.Authentication{}, before, V.send_of(returns))
    case Some{context}:
      match returns:
        case V.Returns{check, allocation, seal, send}: checked(c, position, check, mode, raw, context, before, allocation, seal, send, selection)


law actual_preparation_derives_its_entire_exact_event_history_and_snapshot:
  for ~c: S.Configuration
  for +world: Nat
  for +input: X.Reception
  for +mode: V.Mode
  for +raw: P.Request
  for +before: E.Snapshot
  for +returns: V.Returns
  Sound(J.Position{world, input, E.database(before)}, V.run(c, mode, raw, before, returns), before)
def actual_preparation_derives_its_entire_exact_event_history_and_snapshot(c, world, input, mode, raw, before, returns):
  +position: J.Position = J.Position{world, input, E.database(before)}
  +identity = D.authenticate(E.database(before), I.credential(raw))
  push(position, V.WireReceived{W.Extension{V.operation(mode), raw}},
    V.push(V.IdentityEstablished{W.Extension{V.operation(mode), raw}, identity}, V.authenticated(c, identity, mode, raw, before, returns)), before, {==},
    push(position, V.IdentityEstablished{W.Extension{V.operation(mode), raw}, identity}, V.authenticated(c, identity, mode, raw, before, returns), before, {==},
      authenticated(c, position, identity, mode, raw, before, returns, {==})))
