# Every actual prepared RECEIPT frame retains original earlier authorization
# and handle selection, including seal pending/failure and registration error.
# No native certificate, freshness, completed receipt or later seal is assumed.
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
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../model/FrameBounds.bend as B
import ../../../../Foundations.bend as F

# All fields are original DATA or literal equalities of DATA. Nothing stores
# an opaque validity, checker certificate, desired trace or completed outcome.
type Cause<-c: S.Configuration, -mode: V.Mode, -raw: P.Request, -before: E.Snapshot,
  -returns: V.Returns, -event: V.PreparationEvent> is Data:
  Cause{context: D.Context, handle: String, seal: V.SealReturn, bytes: List<&2, U32>, send: V.SendReturn,
    authenticated: {D.authenticate(E.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
    returned: {returns == V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, seal, send} : V.Returns},
    fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})) == True{} : Bool},
    frame: {W.frame_receipt(W.PreparedReceipt{handle}) == Some{bytes} : Maybe<&2, List<&2, U32>>},
    payload: {event == V.ReceiptPrepared{W.PreparedReceipt{handle}, bytes} : V.PreparationEvent}}

def Claim(-c: S.Configuration, -mode: V.Mode, -raw: P.Request, -before: E.Snapshot, -returns: V.Returns, event: V.PreparationEvent) -> Type:
  match event:
    case V.ReceiptPrepared{receipt, bytes}: Cause<c, mode, raw, before, returns, V.ReceiptPrepared{receipt, bytes}>
    case _: Unit

def All(-c: S.Configuration, -mode: V.Mode, -raw: P.Request, -before: E.Snapshot, -returns: V.Returns,
  events: List<&2, V.PreparationEvent>) -> Type:
  match events:
    case Nil{}: Unit
    case Con{event, rest}: L.E<Claim(c, mode, raw, before, returns, event), All(c, mode, raw, before, returns, rest)>

def Quiet(event: V.PreparationEvent) -> Type:
  match event:
    case V.ReceiptPrepared{receipt, bytes}: Empty
    case _: Unit

def AllQuiet(events: List<&2, V.PreparationEvent>) -> Type:
  match events:
    case Nil{}: Unit
    case Con{event, rest}: L.E<Quiet(event), AllQuiet(rest)>

def quiet_claim(-c: S.Configuration, -mode: V.Mode, -raw: P.Request, -before: E.Snapshot, -returns: V.Returns,
  event: V.PreparationEvent, quiet: Quiet(event)) -> Claim(c, mode, raw, before, returns, event):
  match event:
    case V.ReceiptConcluded{receipt, result, snapshot, closes}: Unit{}
    case V.WireReceived{wire}: Unit{}
    case V.IdentityEstablished{wire, context}: Unit{}
    case V.Accepted{wire, context}: Unit{}
    case V.Refuted{wire, context}: Unit{}
    case V.PrimitiveFailed{stage, identifier, fatal}: Unit{}
    case V.HandleChosen{handle}: Unit{}
    case V.ReceiptPrepared{receipt, bytes}: L.ex_false(Claim(c, mode, raw, before, returns, V.ReceiptPrepared{receipt, bytes}), quiet)
    case V.ArtifactSealed{entry}: Unit{}
    case V.RegistryChanged{entry, before, after}: Unit{}
    case V.ErrorPrepared{status, bytes}: Unit{}
    case V.ErrorConcluded{status, snapshot, closes}: Unit{}
    case V.Delivered{bytes}: Unit{}
    case V.Interrupted{prefix}: Unit{}
    case V.Closed{}: Unit{}

def lift_quiet(-c: S.Configuration, -mode: V.Mode, -raw: P.Request, -before: E.Snapshot, -returns: V.Returns,
  events: List<&2, V.PreparationEvent>, quiet: AllQuiet(events)) -> All(c, mode, raw, before, returns, events):
  match events quiet:
    case Nil{} unit: Unit{}
    case Con{event, rest} L.Both{head, tail}:
      L.Both{quiet_claim(c, mode, raw, before, returns, event, head), lift_quiet(c, mode, raw, before, returns, rest, tail)}

def quiet_delivery(+send: V.SendReturn, +bytes: List<&2, U32>, +result: H.ControlResult, +snapshot: E.Snapshot) -> AllQuiet(V.events(V.delivery(send, bytes, result, snapshot))):
  match send:
    case V.SendPending{}: Unit{}
    case V.SendComplete{}: L.Both{Unit{}, Unit{}}
    case V.SendInterrupted{prefix}: L.Both{Unit{}, L.Both{Unit{}, Unit{}}}

def quiet_prepend(+event: V.PreparationEvent, +run: V.PreparationRun,
  head: Quiet(event), tail: AllQuiet(V.events(run))) -> AllQuiet(V.events(V.push(event, run))):
  match run:
    case V.PreparationRun{events, result, snapshot, waiting, closed}: L.Both{head, tail}

def quiet_error_frame(+status: S.Status, +before: E.Snapshot, +send: V.SendReturn, frame: Maybe<&2, List<&2, U32>>) ->
  AllQuiet(V.events(V.error_framed(status, before, send, frame))):
  match frame:
    case None{}: Unit{}
    case Some{+bytes}:
      quiet_prepend(V.ErrorPrepared{status, bytes}, V.push(V.ErrorConcluded{status, before, False{}}, V.delivery(send, bytes, H.ControlResult{E.database(before), E.registry(before), H.Error{status}}, before)), Unit{},
        quiet_prepend(V.ErrorConcluded{status, before, False{}}, V.delivery(send, bytes, H.ControlResult{E.database(before), E.registry(before), H.Error{status}}, before), Unit{},
          quiet_delivery(send, bytes, H.ControlResult{E.database(before), E.registry(before), H.Error{status}}, before)))

def quiet_error(+status: S.Status, +before: E.Snapshot, +send: V.SendReturn) -> AllQuiet(V.events(V.error(status, before, send))):
  quiet_error_frame(status, before, send, P.frame(S.response_value(S.response_error(status))))

def quiet_failed(+stage: X.Stage, +identifier: String, fatal: Bool, +before: E.Snapshot, +send: V.SendReturn) ->
  AllQuiet(V.events(V.failed(stage, identifier, fatal, before, send))):
  match fatal:
    case True{}: L.Both{Unit{}, L.Both{Unit{}, Unit{}}}
    case False{}:
      quiet_prepend(V.PrimitiveFailed{stage, identifier, False{}}, V.error(S.Failure{}, before, send), Unit{}, quiet_error(S.Failure{}, before, send))

def prepend(-c: S.Configuration, -mode: V.Mode, -raw: P.Request, -before: E.Snapshot, -returns: V.Returns,
  +event: V.PreparationEvent, +run: V.PreparationRun,
  head: Claim(c, mode, raw, before, returns, event), tail: All(c, mode, raw, before, returns, V.events(run))) ->
  All(c, mode, raw, before, returns, V.events(V.push(event, run))):
  match run:
    case V.PreparationRun{events, result, snapshot, waiting, closed}: L.Both{head, tail}

def quiet_register_result(completed: H.ControlResult, +before: E.Snapshot, +entry: G.Entry, +bytes: List<&2, U32>, +send: V.SendReturn) -> AllQuiet(V.events(V.register_result(completed, before, entry, bytes, send))):
  match completed:
    case H.ControlResult{state, entries, H.Error{status}}: quiet_error(status, before, send)
    case H.ControlResult{state, entries, H.Metadata{+receipt}}:
      +actual: H.ControlResult = H.ControlResult{state, entries, H.Metadata{receipt}}
      +after = V.registered_snapshot(before, actual)
      quiet_prepend(V.RegistryChanged{entry, before, after}, V.push(V.ReceiptConcluded{receipt, actual, after, False{}}, V.delivery(send, bytes, actual, after)), Unit{},
        quiet_prepend(V.ReceiptConcluded{receipt, actual, after, False{}}, V.delivery(send, bytes, actual, after), Unit{}, quiet_delivery(send, bytes, actual, after)))


def quiet_sealed(~c: S.Configuration, +mode: V.Mode, +raw: P.Request, +before: E.Snapshot,
  +handle: String, seal: V.SealReturn, +bytes: List<&2, U32>, +send: V.SendReturn) -> AllQuiet(V.events(V.seal_result(c, seal, mode, raw, before, handle, bytes, send))):
  match seal:
    case V.SealPending{}: Unit{}
    case V.SealFailed{stage, identifier, fatal}: quiet_failed(stage, identifier, fatal, before, send)
    case V.SealSucceeded{+seal}:
      quiet_prepend(V.ArtifactSealed{V.entry(mode, raw, E.instance(before), handle, seal)},
        V.register_result(H.register(c, E.database(before), E.instance(before), V.entry(mode, raw, E.instance(before), handle, seal), E.registry(before)), before, V.entry(mode, raw, E.instance(before), handle, seal), bytes, send), Unit{},
        quiet_register_result(H.register(c, E.database(before), E.instance(before), V.entry(mode, raw, E.instance(before), handle, seal), E.registry(before)), before, V.entry(mode, raw, E.instance(before), handle, seal), bytes, send))


def framed(~c: S.Configuration, frame: Maybe<&2, List<&2, U32>>, +mode: V.Mode, +raw: P.Request, +before: E.Snapshot,
  +context: D.Context, +handle: String, +seal: V.SealReturn, +send: V.SendReturn,
  +authenticated: {D.authenticate(E.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
  +fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})) == True{} : Bool},
  +actual: {W.frame_receipt(W.PreparedReceipt{handle}) == frame : Maybe<&2, List<&2, U32>>}) ->
  All(c, mode, raw, before, V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, seal, send},
    V.events(V.fitting_frame(c, frame, mode, raw, before, handle, seal, send))):
  match frame:
    case None{}: Unit{}
    case Some{+bytes}:
      prepend(c, mode, raw, before, V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, seal, send}, V.ReceiptPrepared{W.PreparedReceipt{handle}, bytes},
        V.seal_result(c, seal, mode, raw, before, handle, bytes, send),
        Cause{context, handle, seal, bytes, send, authenticated, {==}, fits, actual, {==}},
        lift_quiet(c, mode, raw, before, V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, seal, send}, V.events(V.seal_result(c, seal, mode, raw, before, handle, bytes, send)), quiet_sealed(c, mode, raw, before, handle, seal, bytes, send)))

def fitting(~c: S.Configuration, fits: Bool, +mode: V.Mode, +raw: P.Request, +before: E.Snapshot,
  +context: D.Context, +handle: String, +seal: V.SealReturn, +send: V.SendReturn,
  +authenticated: {D.authenticate(E.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
  +actual: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})) == fits : Bool}) ->
  All(c, mode, raw, before, V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, seal, send},
    V.events(V.receipt_fit(c, fits, mode, raw, before, handle, seal, send))):
  match fits:
    case False{}:
      lift_quiet(c, mode, raw, before, V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, seal, send}, V.events(V.error(S.Limit{}, before, send)), quiet_error(S.Limit{}, before, send))
    case True{}:
      framed(c, W.frame_receipt(W.PreparedReceipt{handle}), mode, raw, before, context, handle, seal, send, authenticated, actual, {==})

def allocated(~c: S.Configuration, +mode: V.Mode, +raw: P.Request, +before: E.Snapshot,
  +context: D.Context, +allocation: V.AllocatorReturn, +seal: V.SealReturn, +send: V.SendReturn,
  +authenticated: {D.authenticate(E.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>}) ->
  All(c, mode, raw, before, V.Returns{V.CheckerAccepted{}, allocation, seal, send},
    V.events(V.allocated(c, allocation, mode, raw, before, seal, send))):
  match allocation:
    case V.AllocatorPending{}: Unit{}
    case V.AllocatorFailed{+stage, +identifier, +fatal}:
      lift_quiet(c, mode, raw, before, V.Returns{V.CheckerAccepted{}, V.AllocatorFailed{stage, identifier, fatal}, seal, send},
        V.events(V.failed(stage, identifier, fatal, before, send)), quiet_failed(stage, identifier, fatal, before, send))
    case V.AllocatorChosen{+handle}:
      prepend(c, mode, raw, before, V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, seal, send}, V.HandleChosen{handle},
        V.receipt_fit(c, R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})), mode, raw, before, handle, seal, send), Unit{},
        fitting(c, R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})), mode, raw, before, context, handle, seal, send, authenticated, {==}))

def checked(~c: S.Configuration, +mode: V.Mode, +raw: P.Request, +before: E.Snapshot,
  +context: D.Context, +check: V.CheckerReturn, +allocation: V.AllocatorReturn, +seal: V.SealReturn, +send: V.SendReturn,
  +authenticated: {D.authenticate(E.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>}) ->
  All(c, mode, raw, before, V.Returns{check, allocation, seal, send},
    V.events(V.checked(c, check, mode, raw, context, before, allocation, seal, send))):
  match check:
    case V.CheckerPending{}: Unit{}
    case V.CheckerFailed{+stage, +identifier, +fatal}:
      lift_quiet(c, mode, raw, before, V.Returns{V.CheckerFailed{stage, identifier, fatal}, allocation, seal, send},
        V.events(V.failed(stage, identifier, fatal, before, send)), quiet_failed(stage, identifier, fatal, before, send))
    case V.CheckerRefuted{}:
      prepend(c, mode, raw, before, V.Returns{V.CheckerRefuted{}, allocation, seal, send}, V.Refuted{W.Extension{V.operation(mode), raw}, context},
        V.error(S.Certificate{}, before, send), Unit{},
        lift_quiet(c, mode, raw, before, V.Returns{V.CheckerRefuted{}, allocation, seal, send}, V.events(V.error(S.Certificate{}, before, send)), quiet_error(S.Certificate{}, before, send)))
    case V.CheckerAccepted{}:
      prepend(c, mode, raw, before, V.Returns{V.CheckerAccepted{}, allocation, seal, send}, V.Accepted{W.Extension{V.operation(mode), raw}, context},
        V.allocated(c, allocation, mode, raw, before, seal, send), Unit{}, allocated(c, mode, raw, before, context, allocation, seal, send, authenticated))

def authenticated(~c: S.Configuration, identity: Maybe<&2, D.Context>, +mode: V.Mode, +raw: P.Request, +before: E.Snapshot, +returns: V.Returns,
  +actual: {D.authenticate(E.database(before), I.credential(raw)) == identity : Maybe<&2, D.Context>}) ->
  All(c, mode, raw, before, returns, V.events(V.authenticated(c, identity, mode, raw, before, returns))):
  match identity:
    case None{}:
      lift_quiet(c, mode, raw, before, returns, V.events(V.error(S.Authentication{}, before, V.send_of(returns))), quiet_error(S.Authentication{}, before, V.send_of(returns)))
    case Some{+context}:
      match returns:
        case V.Returns{+check, +allocation, +seal, +send}: checked(c, mode, raw, before, context, check, allocation, seal, send, actual)

law every_actual_prepared_receipt_retains_its_reached_authentication_acceptance_handle_and_frame:
  for ~c: S.Configuration
  for +mode: V.Mode
  for +raw: P.Request
  for +before: E.Snapshot
  for +returns: V.Returns
  All(c, mode, raw, before, returns, V.events(V.run(c, mode, raw, before, returns)))
def every_actual_prepared_receipt_retains_its_reached_authentication_acceptance_handle_and_frame(c, mode, raw, before, returns):
  prepend(c, mode, raw, before, returns, V.WireReceived{W.Extension{V.operation(mode), raw}},
    V.push(V.IdentityEstablished{W.Extension{V.operation(mode), raw}, D.authenticate(E.database(before), I.credential(raw))},
      V.authenticated(c, D.authenticate(E.database(before), I.credential(raw)), mode, raw, before, returns)), Unit{},
    prepend(c, mode, raw, before, returns, V.IdentityEstablished{W.Extension{V.operation(mode), raw}, D.authenticate(E.database(before), I.credential(raw))},
      V.authenticated(c, D.authenticate(E.database(before), I.credential(raw)), mode, raw, before, returns), Unit{},
      authenticated(c, D.authenticate(E.database(before), I.credential(raw)), mode, raw, before, returns, {==})))

def query(~c: S.Configuration, +mode: V.Mode, +raw: P.Request, +before: E.Snapshot, +returns: V.Returns,
  +events: List<&2, V.PreparationEvent>, index: Nat, +event: V.PreparationEvent,
  causes: All(c, mode, raw, before, returns, events), found: {B.query(V.PreparationEvent, events, index) == Some{event} : Maybe<&2, V.PreparationEvent>}) ->
  Claim(c, mode, raw, before, returns, event):
  match events index causes:
    case Nil{} _ unit: L.ex_false(Claim(c, mode, raw, before, returns, event), F.none_negative_some(V.PreparationEvent, event, found))
    case Con{+head, rest} Zero{} L.Both{claim, tail}:
      %F.some_injective(V.PreparationEvent, head, event, found) : Claim(c, mode, raw, before, returns, _)
      claim
    case Con{head, +rest} Succ{prior} L.Both{claim, tail}: query(c, mode, raw, before, returns, rest, prior, event, tail, found)


law any_actual_queried_prepared_receipt_recovers_its_original_inputs_before_any_seal_result:
  for ~c: S.Configuration
  for +mode: V.Mode
  for +raw: P.Request
  for +before: E.Snapshot
  for +returns: V.Returns
  for +index: Nat
  for +receipt: W.Receipt
  for +bytes: List<&2, U32>
  for found: {B.query(V.PreparationEvent, V.events(V.run(c, mode, raw, before, returns)), index) == Some{V.ReceiptPrepared{receipt, bytes}} : Maybe<&2, V.PreparationEvent>}
  Cause<c, mode, raw, before, returns, V.ReceiptPrepared{receipt, bytes}>
def any_actual_queried_prepared_receipt_recovers_its_original_inputs_before_any_seal_result(c, mode, raw, before, returns, index, receipt, bytes, found):
  query(c, mode, raw, before, returns, V.events(V.run(c, mode, raw, before, returns)), index, V.ReceiptPrepared{receipt, bytes},
    every_actual_prepared_receipt_retains_its_reached_authentication_acceptance_handle_and_frame(c, mode, raw, before, returns), found)
