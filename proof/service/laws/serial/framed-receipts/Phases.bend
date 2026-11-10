# Actual preparation/invalidation ReceiptPrepared is encoded and bounded EVEN
# when a later seal/registration/cleanup/send never completes. No success,
# authenticity, readiness, completed outcome or caller-supplied frame premise.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Interface.bend as I
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
import ../../../phases/InvalidationPhases.bend as N

def Receipt(~c: S.Configuration, receipt: W.Receipt, bytes: List<&2, U32>) -> Type:
  L.E<W.ReceiptEncoding(receipt, bytes), {R.fits(R.limit_response(S.limits(c)), W.receipt_value(receipt)) == True{} : Bool}>

def Claim(~c: S.Configuration, phase: V.PreparationEvent) -> Type:
  match phase:
    case V.ReceiptPrepared{receipt, bytes}: Receipt(c, receipt, bytes)
    case _: Unit

def All(~c: S.Configuration, phases: List<&2, V.PreparationEvent>) -> Type:
  match phases:
    case Nil{}: Unit
    case Con{phase, rest}: L.E<Claim(c, phase), All(c, rest)>

def pushed(~c: S.Configuration, +phase: V.PreparationEvent, run: V.PreparationRun, first: Claim(c, phase), later: All(c, V.events(run))) -> All(c, V.events(V.push(phase, run))):
  match run:
    case V.PreparationRun{events, result, snapshot, waiting, closed}: L.Both{first, later}

def delivery(~c: S.Configuration, send: V.SendReturn, bytes: List<&2, U32>, completed: H.ControlResult, snapshot: E.Snapshot) -> All(c, V.events(V.delivery(send, bytes, completed, snapshot))):
  match send:
    case V.SendPending{}: Unit{}
    case V.SendComplete{}: L.Both{Unit{}, Unit{}}
    case V.SendInterrupted{prefix}: L.Both{Unit{}, L.Both{Unit{}, Unit{}}}

def error_framed(~c: S.Configuration, +status: S.Status, +snapshot: E.Snapshot, +send: V.SendReturn, frame: Maybe<&2, List<&2, U32>>) -> All(c, V.events(V.error_framed(status, snapshot, send, frame))):
  match frame:
    case None{}: Unit{}
    case Some{+bytes}:
      pushed(c, V.ErrorPrepared{status, bytes}, V.push(V.ErrorConcluded{status, snapshot, False{}}, V.delivery(send, bytes, H.ControlResult{E.database(snapshot), E.registry(snapshot), H.Error{status}}, snapshot)), Unit{},
        pushed(c, V.ErrorConcluded{status, snapshot, False{}}, V.delivery(send, bytes, H.ControlResult{E.database(snapshot), E.registry(snapshot), H.Error{status}}, snapshot), Unit{},
          delivery(c, send, bytes, H.ControlResult{E.database(snapshot), E.registry(snapshot), H.Error{status}}, snapshot)))

def error(~c: S.Configuration, +status: S.Status, snapshot: E.Snapshot, send: V.SendReturn) -> All(c, V.events(V.error(status, snapshot, send))):
  error_framed(c, status, snapshot, send, P.frame(S.response_value(S.response_error(status))))

def failed(~c: S.Configuration, +stage: X.Stage, +identifier: String, fatal: Bool, +snapshot: E.Snapshot, +send: V.SendReturn) -> All(c, V.events(V.failed(stage, identifier, fatal, snapshot, send))):
  match fatal:
    case True{}: L.Both{Unit{}, L.Both{Unit{}, Unit{}}}
    case False{}: pushed(c, V.PrimitiveFailed{stage, identifier, False{}}, V.error(S.Failure{}, snapshot, send), Unit{}, error(c, S.Failure{}, snapshot, send))

def registered(~c: S.Configuration, completed: H.ControlResult, +before: E.Snapshot, +entry: G.Entry, +bytes: List<&2, U32>, +send: V.SendReturn) -> All(c, V.events(V.register_result(completed, before, entry, bytes, send))):
  match completed:
    case H.ControlResult{+state, +entries, H.Metadata{+receipt}}:
      pushed(c, V.RegistryChanged{entry, before, V.registered_snapshot(before, H.ControlResult{state, entries, H.Metadata{receipt}})},
        V.push(V.ReceiptConcluded{receipt, H.ControlResult{state, entries, H.Metadata{receipt}}, V.registered_snapshot(before, H.ControlResult{state, entries, H.Metadata{receipt}}), False{}},
          V.delivery(send, bytes, H.ControlResult{state, entries, H.Metadata{receipt}}, V.registered_snapshot(before, H.ControlResult{state, entries, H.Metadata{receipt}}))), Unit{},
        pushed(c, V.ReceiptConcluded{receipt, H.ControlResult{state, entries, H.Metadata{receipt}}, V.registered_snapshot(before, H.ControlResult{state, entries, H.Metadata{receipt}}), False{}},
          V.delivery(send, bytes, H.ControlResult{state, entries, H.Metadata{receipt}}, V.registered_snapshot(before, H.ControlResult{state, entries, H.Metadata{receipt}})), Unit{},
          delivery(c, send, bytes, H.ControlResult{state, entries, H.Metadata{receipt}}, V.registered_snapshot(before, H.ControlResult{state, entries, H.Metadata{receipt}}))))
    case H.ControlResult{state, entries, H.Error{status}}: error(c, status, before, send)

def sealed(~c: S.Configuration, seal: V.SealReturn, +mode: V.Mode, +raw: P.Request, +before: E.Snapshot, +handle: String, +bytes: List<&2, U32>, +send: V.SendReturn) -> All(c, V.events(V.seal_result(c, seal, mode, raw, before, handle, bytes, send))):
  match seal:
    case V.SealPending{}: Unit{}
    case V.SealFailed{stage, identifier, fatal}: failed(c, stage, identifier, fatal, before, send)
    case V.SealSucceeded{+seal}:
      pushed(c, V.ArtifactSealed{V.entry(mode, raw, E.instance(before), handle, seal)},
        V.register_result(H.register(c, E.database(before), E.instance(before), V.entry(mode, raw, E.instance(before), handle, seal), E.registry(before)), before, V.entry(mode, raw, E.instance(before), handle, seal), bytes, send), Unit{},
        registered(c, H.register(c, E.database(before), E.instance(before), V.entry(mode, raw, E.instance(before), handle, seal), E.registry(before)), before, V.entry(mode, raw, E.instance(before), handle, seal), bytes, send))

def framed(~c: S.Configuration, frame: Maybe<&2, List<&2, U32>>, +mode: V.Mode, +raw: P.Request, +before: E.Snapshot, +handle: String, +seal: V.SealReturn, +send: V.SendReturn,
  fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})) == True{} : Bool},
  encoded: {W.frame_receipt(W.PreparedReceipt{handle}) == frame : Maybe<&2, List<&2, U32>>}) -> All(c, V.events(V.fitting_frame(c, frame, mode, raw, before, handle, seal, send))):
  match frame:
    case None{}: Unit{}
    case Some{+bytes}: pushed(c, V.ReceiptPrepared{W.PreparedReceipt{handle}, bytes}, V.seal_result(c, seal, mode, raw, before, handle, bytes, send), L.Both{encoded, fits}, sealed(c, seal, mode, raw, before, handle, bytes, send))

def fitting(~c: S.Configuration, fit: Bool, +mode: V.Mode, +raw: P.Request, +before: E.Snapshot, +handle: String, +seal: V.SealReturn, +send: V.SendReturn,
  exact: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})) == fit : Bool}) -> All(c, V.events(V.receipt_fit(c, fit, mode, raw, before, handle, seal, send))):
  match fit:
    case False{}: error(c, S.Limit{}, before, send)
    case True{}: framed(c, W.frame_receipt(W.PreparedReceipt{handle}), mode, raw, before, handle, seal, send, exact, {==})

def allocated(~c: S.Configuration, allocation: V.AllocatorReturn, +mode: V.Mode, +raw: P.Request, +before: E.Snapshot, +seal: V.SealReturn, +send: V.SendReturn) -> All(c, V.events(V.allocated(c, allocation, mode, raw, before, seal, send))):
  match allocation:
    case V.AllocatorPending{}: Unit{}
    case V.AllocatorFailed{stage, identifier, fatal}: failed(c, stage, identifier, fatal, before, send)
    case V.AllocatorChosen{+handle}: pushed(c, V.HandleChosen{handle}, V.receipt_fit(c, R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})), mode, raw, before, handle, seal, send), Unit{},
      fitting(c, R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})), mode, raw, before, handle, seal, send, {==}))

def checked(~c: S.Configuration, check: V.CheckerReturn, +mode: V.Mode, +raw: P.Request, +context: D.Context, +before: E.Snapshot, +allocation: V.AllocatorReturn, +seal: V.SealReturn, +send: V.SendReturn) -> All(c, V.events(V.checked(c, check, mode, raw, context, before, allocation, seal, send))):
  match check:
    case V.CheckerPending{}: Unit{}
    case V.CheckerFailed{stage, identifier, fatal}: failed(c, stage, identifier, fatal, before, send)
    case V.CheckerRefuted{}: pushed(c, V.Refuted{W.Extension{V.operation(mode), raw}, context}, V.error(S.Certificate{}, before, send), Unit{}, error(c, S.Certificate{}, before, send))
    case V.CheckerAccepted{}: pushed(c, V.Accepted{W.Extension{V.operation(mode), raw}, context}, V.allocated(c, allocation, mode, raw, before, seal, send), Unit{}, allocated(c, allocation, mode, raw, before, seal, send))

def authenticated(~c: S.Configuration, identity: Maybe<&2, D.Context>, +mode: V.Mode, +raw: P.Request, +before: E.Snapshot, +returns: V.Returns) -> All(c, V.events(V.authenticated(c, identity, mode, raw, before, returns))):
  match identity:
    case None{}: error(c, S.Authentication{}, before, V.send_of(returns))
    case Some{context}:
      match returns:
        case V.Returns{checker, allocation, seal, send}: checked(c, checker, mode, raw, context, before, allocation, seal, send)

law every_actual_preparation_receipt_frame_has_its_literal_encoding_and_bound_even_without_later_success:
  for ~c: S.Configuration
  for +mode: V.Mode
  for +raw: P.Request
  for +before: E.Snapshot
  for +returns: V.Returns
  All(c, V.events(V.run(c, mode, raw, before, returns)))
def every_actual_preparation_receipt_frame_has_its_literal_encoding_and_bound_even_without_later_success(c, mode, raw, before, returns):
  pushed(c, V.WireReceived{W.Extension{V.operation(mode), raw}},
    V.push(V.IdentityEstablished{W.Extension{V.operation(mode), raw}, D.authenticate(E.database(before), I.credential(raw))}, V.authenticated(c, D.authenticate(E.database(before), I.credential(raw)), mode, raw, before, returns)), Unit{},
    pushed(c, V.IdentityEstablished{W.Extension{V.operation(mode), raw}, D.authenticate(E.database(before), I.credential(raw))}, V.authenticated(c, D.authenticate(E.database(before), I.credential(raw)), mode, raw, before, returns), Unit{},
      authenticated(c, D.authenticate(E.database(before), I.credential(raw)), mode, raw, before, returns)))
