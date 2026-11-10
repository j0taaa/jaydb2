# Actual invalidation never fabricates acceptance or a handle choice. Its
# physical headers, removal, pending/failing cleanup and all delivery remain.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/PreparedRegistry.bend as G
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Requirements.bend as R
import ../../../../../contract/Resources.bend as X
import ../../../../../contract/Semantics.bend as S
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../phases/InvalidationPhases.bend as N
import ../../../model/serial/Common.bend as C
import ../../../model/EventObserver.bend as O
import ./SealingData.bend as Header
import ./Absent.bend as B
import ./PreparationCauses.bend as Preparation


def Tail(+run: N.InvalidationRun) -> Type:
  B.All(C.invalidate_events(N.events(run)))


def lifted_events(+events: List<&2, V.PreparationEvent>, original: Preparation.AllQuiet(events)) -> B.All(C.invalidate_events(N.base_events(events))):
  match events original:
    case Nil{} unit: Unit{}
    case Con{event, +rest} L.Both{head, later}: L.Both{head, lifted_events(rest, later)}


def lifted(run: V.PreparationRun, original: Preparation.AllQuiet(V.events(run))) -> Tail(N.lift(run)):
  match run:
    case V.PreparationRun{events, result, snapshot, waiting, closed}: lifted_events(events, original)


def pushed(+event: N.InvalidationEvent, run: N.InvalidationRun, head: Header.NoSite(O.Invalidation{event}), later: Tail(run)) -> Tail(N.push(event, run)):
  match run:
    case N.InvalidationRun{events, result, snapshot, waiting, closed}: L.Both{head, later}


def cleaned(cleanup: N.CleanupReturn, +after: E.Snapshot, +bytes: List<&2, U32>, +send: V.SendReturn) -> Tail(N.cleaned(cleanup, after, bytes, send)):
  match cleanup:
    case N.CleanupPending{}: lifted(V.pending(after), Unit{})
    case N.CleanupFailed{+identifier, +fatal}: lifted(V.failed(X.Prepare{}, identifier, fatal, after, send), Preparation.quiet_failed(X.Prepare{}, identifier, fatal, after, send))
    case N.CleanupComplete{}:
      lifted(V.push(V.ReceiptConcluded{W.InvalidatedReceipt{}, N.metadata(after), after, False{}}, V.delivery(send, bytes, N.metadata(after), after)),
        Preparation.quiet_prepend(V.ReceiptConcluded{W.InvalidatedReceipt{}, N.metadata(after), after, False{}}, V.delivery(send, bytes, N.metadata(after), after), Unit{}, Preparation.quiet_delivery(send, bytes, N.metadata(after), after)))


def remove_and_cleanup(+before: E.Snapshot, +handle: String, +bytes: List<&2, U32>, +cleanup: N.CleanupReturn, +send: V.SendReturn) -> Tail(N.remove_and_cleanup(before, handle, bytes, cleanup, send)):
  pushed(N.RegistryRemoved{handle, before, N.removed(before, handle)}, N.cleaned(cleanup, N.removed(before, handle), bytes, send), Unit{}, cleaned(cleanup, N.removed(before, handle), bytes, send))


def framed(frame: Maybe<&2, List<&2, U32>>, +before: E.Snapshot, +handle: String, +cleanup: N.CleanupReturn, +send: V.SendReturn) -> Tail(N.framed(frame, before, handle, cleanup, send)):
  match frame:
    case None{}: lifted(V.inconsistent(before), Unit{})
    case Some{+bytes}:
      pushed(N.InvalidationBase{V.ReceiptPrepared{W.InvalidatedReceipt{}, bytes}}, N.remove_and_cleanup(before, handle, bytes, cleanup, send), Unit{}, remove_and_cleanup(before, handle, bytes, cleanup, send))


def fitting(fits: Bool, +before: E.Snapshot, +handle: String, +cleanup: N.CleanupReturn, +send: V.SendReturn) -> Tail(N.fitting(fits, before, handle, cleanup, send)):
  match fits:
    case False{}: lifted(V.error(S.Limit{}, before, send), Preparation.quiet_error(S.Limit{}, before, send))
    case True{}: framed(W.frame_receipt(W.InvalidatedReceipt{}), before, handle, cleanup, send)


def found(~c: S.Configuration, selected: Maybe<&2, G.Entry>, +before: E.Snapshot, +handle: String, +cleanup: N.CleanupReturn, +send: V.SendReturn) -> Tail(N.found(c, selected, before, handle, cleanup, send)):
  match selected:
    case None{}: lifted(V.error(S.Failure{}, before, send), Preparation.quiet_error(S.Failure{}, before, send))
    case Some{entry}: fitting(R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})), before, handle, cleanup, send)


def proof_checked(~c: S.Configuration, empty: Bool, +before: E.Snapshot, +raw: P.Request, +cleanup: N.CleanupReturn, +send: V.SendReturn) -> Tail(N.proof_checked(c, empty, before, raw, cleanup, send)):
  match empty:
    case False{}: lifted(V.error(S.Input{}, before, send), Preparation.quiet_error(S.Input{}, before, send))
    case True{}: found(c, G.lookup(E.instance(before), I.code(raw), E.registry(before)), before, I.code(raw), cleanup, send)


def authenticated(~c: S.Configuration, identity: Maybe<&2, D.Context>, +before: E.Snapshot, +raw: P.Request, +cleanup: N.CleanupReturn, +send: V.SendReturn) -> Tail(N.authenticated(c, identity, before, raw, cleanup, send)):
  match identity:
    case None{}: lifted(V.error(S.Authentication{}, before, send), Preparation.quiet_error(S.Authentication{}, before, send))
    case Some{context}: proof_checked(c, String.eq(I.proof(raw), ""), before, raw, cleanup, send)


def call(run: N.InvalidationRun, original: Tail(run)) -> B.Call(C.invalidation(run)):
  match run:
    case N.InvalidationRun{events, result, snapshot, waiting, closed}: original


def run(~c: S.Configuration, +before: E.Snapshot, +raw: P.Request, +cleanup: N.CleanupReturn, +send: V.SendReturn) -> Tail(N.run(c, before, raw, cleanup, send)):
  pushed(N.InvalidationBase{V.WireReceived{W.Extension{W.Invalidate{}, raw}}},
    N.push(N.InvalidationBase{V.IdentityEstablished{W.Extension{W.Invalidate{}, raw}, D.authenticate(E.database(before), I.credential(raw))}},
      N.authenticated(c, D.authenticate(E.database(before), I.credential(raw)), before, raw, cleanup, send)), Unit{},
    pushed(N.InvalidationBase{V.IdentityEstablished{W.Extension{W.Invalidate{}, raw}, D.authenticate(E.database(before), I.credential(raw))}},
      N.authenticated(c, D.authenticate(E.database(before), I.credential(raw)), before, raw, cleanup, send), Unit{},
      authenticated(c, D.authenticate(E.database(before), I.credential(raw)), before, raw, cleanup, send)))
