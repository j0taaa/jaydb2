# Every actual preparation event AFTER the two host headers is a non-header,
# including mutation, technical failure, pending and delivery branches.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/PreparedLaws.bend as H
import ../../../../../contract/PreparedRegistry.bend as G
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Requirements.bend as R
import ../../../../../contract/Resources.bend as X
import ../../../../../contract/Semantics.bend as S
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../model/serial/Common.bend as C
import ./HeaderData.bend as Header
import ./RuntimeBase.bend as B


def Tail(+run: V.PreparationRun) -> Type:
  B.All(C.prepare_events(V.events(run)))


def pushed(+event: V.PreparationEvent, run: V.PreparationRun, head: Header.NoHeaderPhase(event), later: Tail(run)) -> Tail(V.push(event, run)):
  match run:
    case V.PreparationRun{events, result, snapshot, waiting, closed}: L.Both{head, later}


def delivery(send: V.SendReturn, +bytes: List<&2, U32>, completed: H.ControlResult, before: E.Snapshot) -> Tail(V.delivery(send, bytes, completed, before)):
  match send:
    case V.SendPending{}: Unit{}
    case V.SendComplete{}: L.Both{Unit{}, Unit{}}
    case V.SendInterrupted{prefix}: L.Both{Unit{}, L.Both{Unit{}, Unit{}}}


def error_framed(+status: S.Status, +before: E.Snapshot, +send: V.SendReturn, frame: Maybe<&2, List<&2, U32>>) -> Tail(V.error_framed(status, before, send, frame)):
  match frame:
    case None{}: Unit{}
    case Some{+bytes}:
      pushed(V.ErrorPrepared{status, bytes}, V.push(V.ErrorConcluded{status, before, False{}}, V.delivery(send, bytes, H.ControlResult{E.database(before), E.registry(before), H.Error{status}}, before)), Unit{},
        pushed(V.ErrorConcluded{status, before, False{}}, V.delivery(send, bytes, H.ControlResult{E.database(before), E.registry(before), H.Error{status}}, before), Unit{}, delivery(send, bytes, H.ControlResult{E.database(before), E.registry(before), H.Error{status}}, before)))


def error(+status: S.Status, +before: E.Snapshot, +send: V.SendReturn) -> Tail(V.error(status, before, send)):
  error_framed(status, before, send, P.frame(S.response_value(S.response_error(status))))


def failed(+stage: X.Stage, +identifier: String, fatal: Bool, +before: E.Snapshot, +send: V.SendReturn) -> Tail(V.failed(stage, identifier, fatal, before, send)):
  match fatal:
    case True{}: L.Both{Unit{}, L.Both{Unit{}, Unit{}}}
    case False{}: pushed(V.PrimitiveFailed{stage, identifier, False{}}, V.error(S.Failure{}, before, send), Unit{}, error(S.Failure{}, before, send))


def register_result(completed: H.ControlResult, +before: E.Snapshot, +entry: G.Entry, +bytes: List<&2, U32>, +send: V.SendReturn) -> Tail(V.register_result(completed, before, entry, bytes, send)):
  match completed:
    case H.ControlResult{state, entries, H.Error{status}}: error(status, before, send)
    case H.ControlResult{state, entries, H.Metadata{+receipt}}:
      +actual: H.ControlResult = H.ControlResult{state, entries, H.Metadata{receipt}}
      +after = V.registered_snapshot(before, actual)
      pushed(V.RegistryChanged{entry, before, after}, V.push(V.ReceiptConcluded{receipt, actual, after, False{}}, V.delivery(send, bytes, actual, after)), Unit{},
        pushed(V.ReceiptConcluded{receipt, actual, after, False{}}, V.delivery(send, bytes, actual, after), Unit{}, delivery(send, bytes, actual, after)))


def seal_result(~c: S.Configuration, seal: V.SealReturn, +mode: V.Mode, +raw: P.Request, +before: E.Snapshot, +handle: String, +bytes: List<&2, U32>, +send: V.SendReturn) ->
  Tail(V.seal_result(c, seal, mode, raw, before, handle, bytes, send)):
  match seal:
    case V.SealPending{}: Unit{}
    case V.SealFailed{stage, identifier, fatal}: failed(stage, identifier, fatal, before, send)
    case V.SealSucceeded{seal}:
      +entry = V.entry(mode, raw, E.instance(before), handle, seal)
      pushed(V.ArtifactSealed{entry}, V.register_result(H.register(c, E.database(before), E.instance(before), entry, E.registry(before)), before, entry, bytes, send), Unit{},
        register_result(H.register(c, E.database(before), E.instance(before), entry, E.registry(before)), before, entry, bytes, send))


def fitting_frame(~c: S.Configuration, frame: Maybe<&2, List<&2, U32>>, +mode: V.Mode, +raw: P.Request, +before: E.Snapshot, +handle: String, +seal: V.SealReturn, +send: V.SendReturn) ->
  Tail(V.fitting_frame(c, frame, mode, raw, before, handle, seal, send)):
  match frame:
    case None{}: Unit{}
    case Some{+bytes}:
      pushed(V.ReceiptPrepared{W.PreparedReceipt{handle}, bytes}, V.seal_result(c, seal, mode, raw, before, handle, bytes, send), Unit{}, seal_result(c, seal, mode, raw, before, handle, bytes, send))


def receipt_fit(~c: S.Configuration, fits: Bool, +mode: V.Mode, +raw: P.Request, +before: E.Snapshot, +handle: String, +seal: V.SealReturn, +send: V.SendReturn) ->
  Tail(V.receipt_fit(c, fits, mode, raw, before, handle, seal, send)):
  match fits:
    case False{}: error(S.Limit{}, before, send)
    case True{}: fitting_frame(c, W.frame_receipt(W.PreparedReceipt{handle}), mode, raw, before, handle, seal, send)


def allocated(~c: S.Configuration, allocation: V.AllocatorReturn, +mode: V.Mode, +raw: P.Request, +before: E.Snapshot, +seal: V.SealReturn, +send: V.SendReturn) ->
  Tail(V.allocated(c, allocation, mode, raw, before, seal, send)):
  match allocation:
    case V.AllocatorPending{}: Unit{}
    case V.AllocatorFailed{stage, identifier, fatal}: failed(stage, identifier, fatal, before, send)
    case V.AllocatorChosen{+handle}:
      pushed(V.HandleChosen{handle}, V.receipt_fit(c, R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})), mode, raw, before, handle, seal, send), Unit{},
        receipt_fit(c, R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})), mode, raw, before, handle, seal, send))


def checked(~c: S.Configuration, check: V.CheckerReturn, +mode: V.Mode, +raw: P.Request, +context: D.Context, +before: E.Snapshot, +allocation: V.AllocatorReturn, +seal: V.SealReturn, +send: V.SendReturn) ->
  Tail(V.checked(c, check, mode, raw, context, before, allocation, seal, send)):
  match check:
    case V.CheckerPending{}: Unit{}
    case V.CheckerFailed{stage, identifier, fatal}: failed(stage, identifier, fatal, before, send)
    case V.CheckerRefuted{}: pushed(V.Refuted{W.Extension{V.operation(mode), raw}, context}, V.error(S.Certificate{}, before, send), Unit{}, error(S.Certificate{}, before, send))
    case V.CheckerAccepted{}: pushed(V.Accepted{W.Extension{V.operation(mode), raw}, context}, V.allocated(c, allocation, mode, raw, before, seal, send), Unit{}, allocated(c, allocation, mode, raw, before, seal, send))


def authenticated(~c: S.Configuration, identity: Maybe<&2, D.Context>, +mode: V.Mode, +raw: P.Request, +before: E.Snapshot, returns: V.Returns) ->
  Tail(V.authenticated(c, identity, mode, raw, before, returns)):
  match identity:
    case None{}: error(S.Authentication{}, before, V.send_of(returns))
    case Some{context}:
      match returns:
        case V.Returns{check, allocation, seal, send}: checked(c, check, mode, raw, context, before, allocation, seal, send)


def call(run: V.PreparationRun, proof: Tail(run)) -> B.Call(C.preparation(run)):
  match run:
    case V.PreparationRun{events, result, snapshot, waiting, closed}: proof
