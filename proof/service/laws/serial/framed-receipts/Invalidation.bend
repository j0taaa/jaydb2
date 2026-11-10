# Invalidation frame validity is established BEFORE registry removal and ALL
# cleanup returns. Success/completion and native file properties are not inputs.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/PreparedRegistry.bend as G
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Requirements.bend as R
import ../../../../../contract/Resources.bend as X
import ../../../../../contract/Semantics.bend as S
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../phases/InvalidationPhases.bend as N
import ./Phases.bend as Preparation

def Claim(~c: S.Configuration, phase: N.InvalidationEvent) -> Type:
  match phase:
    case N.InvalidationBase{event}: Preparation.Claim(c, event)
    case N.RegistryRemoved{handle, before, after}: Unit

def All(~c: S.Configuration, phases: List<&2, N.InvalidationEvent>) -> Type:
  match phases:
    case Nil{}: Unit
    case Con{phase, rest}: L.E<Claim(c, phase), All(c, rest)>

def pushed(~c: S.Configuration, +phase: N.InvalidationEvent, run: N.InvalidationRun, first: Claim(c, phase), later: All(c, N.events(run))) -> All(c, N.events(N.push(phase, run))):
  match run:
    case N.InvalidationRun{events, result, snapshot, waiting, closed}: L.Both{first, later}

def lift_events(~c: S.Configuration, phases: List<&2, V.PreparationEvent>, valid: Preparation.All(c, phases)) -> All(c, N.base_events(phases)):
  match phases valid:
    case Nil{} unit: Unit{}
    case Con{head, rest} L.Both{first, later}: L.Both{first, lift_events(c, rest, later)}

def lift(~c: S.Configuration, run: V.PreparationRun, valid: Preparation.All(c, V.events(run))) -> All(c, N.events(N.lift(run))):
  match run:
    case V.PreparationRun{events, result, snapshot, waiting, closed}: lift_events(c, events, valid)

def cleaned(~c: S.Configuration, cleanup: N.CleanupReturn, +after: E.Snapshot, +bytes: List<&2, U32>, +send: V.SendReturn) -> All(c, N.events(N.cleaned(cleanup, after, bytes, send))):
  match cleanup:
    case N.CleanupPending{}: lift(c, V.pending(after), Unit{})
    case N.CleanupFailed{+identifier, +fatal}: lift(c, V.failed(X.Prepare{}, identifier, fatal, after, send), Preparation.failed(c, X.Prepare{}, identifier, fatal, after, send))
    case N.CleanupComplete{}:
      lift(c, V.push(V.ReceiptConcluded{W.InvalidatedReceipt{}, N.metadata(after), after, False{}}, V.delivery(send, bytes, N.metadata(after), after)),
        Preparation.pushed(c, V.ReceiptConcluded{W.InvalidatedReceipt{}, N.metadata(after), after, False{}}, V.delivery(send, bytes, N.metadata(after), after), Unit{}, Preparation.delivery(c, send, bytes, N.metadata(after), after)))

def removal(~c: S.Configuration, +before: E.Snapshot, +handle: String, +bytes: List<&2, U32>, +cleanup: N.CleanupReturn, +send: V.SendReturn) -> All(c, N.events(N.remove_and_cleanup(before, handle, bytes, cleanup, send))):
  pushed(c, N.RegistryRemoved{handle, before, N.removed(before, handle)}, N.cleaned(cleanup, N.removed(before, handle), bytes, send), Unit{}, cleaned(c, cleanup, N.removed(before, handle), bytes, send))

def framed(~c: S.Configuration, frame: Maybe<&2, List<&2, U32>>, +before: E.Snapshot, +handle: String, +cleanup: N.CleanupReturn, +send: V.SendReturn,
  fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})) == True{} : Bool},
  encoded: {W.frame_receipt(W.InvalidatedReceipt{}) == frame : Maybe<&2, List<&2, U32>>}) -> All(c, N.events(N.framed(frame, before, handle, cleanup, send))):
  match frame:
    case None{}: lift(c, V.inconsistent(before), Unit{})
    case Some{+bytes}: pushed(c, N.InvalidationBase{V.ReceiptPrepared{W.InvalidatedReceipt{}, bytes}}, N.remove_and_cleanup(before, handle, bytes, cleanup, send), L.Both{encoded, fits}, removal(c, before, handle, bytes, cleanup, send))

def fitting(~c: S.Configuration, fit: Bool, +before: E.Snapshot, +handle: String, +cleanup: N.CleanupReturn, +send: V.SendReturn,
  exact: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})) == fit : Bool}) -> All(c, N.events(N.fitting(fit, before, handle, cleanup, send))):
  match fit:
    case False{}: lift(c, V.error(S.Limit{}, before, send), Preparation.error(c, S.Limit{}, before, send))
    case True{}: framed(c, W.frame_receipt(W.InvalidatedReceipt{}), before, handle, cleanup, send, exact, {==})

def found(~c: S.Configuration, selected: Maybe<&2, G.Entry>, +before: E.Snapshot, +handle: String, +cleanup: N.CleanupReturn, +send: V.SendReturn) -> All(c, N.events(N.found(c, selected, before, handle, cleanup, send))):
  match selected:
    case None{}: lift(c, V.error(S.Failure{}, before, send), Preparation.error(c, S.Failure{}, before, send))
    case Some{entry}: fitting(c, R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})), before, handle, cleanup, send, {==})

def proof_checked(~c: S.Configuration, empty: Bool, +before: E.Snapshot, +raw: P.Request, +cleanup: N.CleanupReturn, +send: V.SendReturn) -> All(c, N.events(N.proof_checked(c, empty, before, raw, cleanup, send))):
  match empty:
    case False{}: lift(c, V.error(S.Input{}, before, send), Preparation.error(c, S.Input{}, before, send))
    case True{}: found(c, G.lookup(E.instance(before), I.code(raw), E.registry(before)), before, I.code(raw), cleanup, send)

def authenticated(~c: S.Configuration, identity: Maybe<&2, D.Context>, +before: E.Snapshot, +raw: P.Request, +cleanup: N.CleanupReturn, +send: V.SendReturn) -> All(c, N.events(N.authenticated(c, identity, before, raw, cleanup, send))):
  match identity:
    case None{}: lift(c, V.error(S.Authentication{}, before, send), Preparation.error(c, S.Authentication{}, before, send))
    case Some{context}: proof_checked(c, String.eq(I.proof(raw), ""), before, raw, cleanup, send)

law every_actual_invalidation_receipt_frame_is_encoded_and_bounded_before_any_cleanup_return:
  for ~c: S.Configuration
  for +before: E.Snapshot
  for +raw: P.Request
  for +cleanup: N.CleanupReturn
  for +send: V.SendReturn
  All(c, N.events(N.run(c, before, raw, cleanup, send)))
def every_actual_invalidation_receipt_frame_is_encoded_and_bounded_before_any_cleanup_return(c, before, raw, cleanup, send):
  pushed(c, N.InvalidationBase{V.WireReceived{W.Extension{W.Invalidate{}, raw}}},
    N.push(N.InvalidationBase{V.IdentityEstablished{W.Extension{W.Invalidate{}, raw}, D.authenticate(E.database(before), I.credential(raw))}}, N.authenticated(c, D.authenticate(E.database(before), I.credential(raw)), before, raw, cleanup, send)), Unit{},
    pushed(c, N.InvalidationBase{V.IdentityEstablished{W.Extension{W.Invalidate{}, raw}, D.authenticate(E.database(before), I.credential(raw))}}, N.authenticated(c, D.authenticate(E.database(before), I.credential(raw)), before, raw, cleanup, send), Unit{},
      authenticated(c, D.authenticate(E.database(before), I.credential(raw)), before, raw, cleanup, send)))
