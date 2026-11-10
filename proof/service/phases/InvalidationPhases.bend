# Actual invalidation order: authenticate, require empty proof, look up the
# handle, frame a bounded receipt, remove the entry, then attempt cleanup.
# A pending/failed cleanup cannot erase the already completed removal.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Interface.bend as I
import ../../../contract/PreparedLaws.bend as H
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/PreparedRegistry.bend as G
import ../../../contract/Protocol.bend as P
import ../../../contract/Requirements.bend as R
import ../../../contract/Resources.bend as X
import ../../../contract/Semantics.bend as S
import ../../SourceService.bend as Source
import ../specification/ServiceLaws.bend as E
import ./PreparePhases.bend as V

type CleanupReturn is Data:
  CleanupPending{}
  CleanupComplete{}
  CleanupFailed{identifier: String, fatal: Bool}

type InvalidationEvent is Data:
  InvalidationBase{event: V.PreparationEvent}
  RegistryRemoved{handle: String, before: E.Snapshot, after: E.Snapshot}

type InvalidationRun is Data:
  InvalidationRun{events: List<&2, InvalidationEvent>, result: Maybe<&2, H.ControlResult>, snapshot: E.Snapshot, waiting: Bool, closed: Bool}

def base_events(events: List<&2, V.PreparationEvent>) -> List<&2, InvalidationEvent>:
  match events:
    case Nil{}: Nil{}
    case Con{event, rest}: Con{InvalidationBase{event}, base_events(rest)}

def lift(run: V.PreparationRun) -> InvalidationRun:
  V.PreparationRun{events, result, snapshot, waiting, closed} = run
  InvalidationRun{base_events(events), result, snapshot, waiting, closed}

def events(run: InvalidationRun) -> List<&2, InvalidationEvent>:
  InvalidationRun{events, result, snapshot, waiting, closed} = run
  events

def result(run: InvalidationRun) -> Maybe<&2, H.ControlResult>:
  InvalidationRun{events, result, snapshot, waiting, closed} = run
  result

def snapshot(run: InvalidationRun) -> E.Snapshot:
  InvalidationRun{events, result, snapshot, waiting, closed} = run
  snapshot

def push(event: InvalidationEvent, run: InvalidationRun) -> InvalidationRun:
  InvalidationRun{events, result, snapshot, waiting, closed} = run
  InvalidationRun{Con{event, events}, result, snapshot, waiting, closed}

def removed(+before: E.Snapshot, handle: String) -> E.Snapshot:
  E.Snapshot{E.instance(before), E.database(before), E.last_response(before), G.remove(E.instance(before), handle, E.registry(before))}

def metadata(+after: E.Snapshot) -> H.ControlResult:
  H.ControlResult{E.database(after), E.registry(after), H.Metadata{W.InvalidatedReceipt{}}}

def cleaned(cleanup: CleanupReturn, +after: E.Snapshot, +bytes: List<&2, U32>, send: V.SendReturn) -> InvalidationRun:
  match cleanup:
    case CleanupPending{}: lift(V.pending(after))
    case CleanupFailed{identifier, fatal}: lift(V.failed(X.Prepare{}, identifier, fatal, after, send))
    case CleanupComplete{}:
      lift(V.push(V.ReceiptConcluded{W.InvalidatedReceipt{}, metadata(after), after, False{}},
        V.delivery(send, bytes, metadata(after), after)))

def remove_and_cleanup(+before: E.Snapshot, +handle: String, +bytes: List<&2, U32>, cleanup: CleanupReturn, send: V.SendReturn) -> InvalidationRun:
  +after = removed(before, handle)
  push(RegistryRemoved{handle, before, after}, cleaned(cleanup, after, bytes, send))

def framed(frame: Maybe<&2, List<&2, U32>>, before: E.Snapshot, handle: String, cleanup: CleanupReturn, send: V.SendReturn) -> InvalidationRun:
  match frame:
    case None{}: lift(V.inconsistent(before))
    case Some{+bytes}:
      push(InvalidationBase{V.ReceiptPrepared{W.InvalidatedReceipt{}, bytes}}, remove_and_cleanup(before, handle, bytes, cleanup, send))

def fitting(fits: Bool, before: E.Snapshot, handle: String, cleanup: CleanupReturn, send: V.SendReturn) -> InvalidationRun:
  match fits:
    case False{}: lift(V.error(S.Limit{}, before, send))
    case True{}: framed(W.frame_receipt(W.InvalidatedReceipt{}), before, handle, cleanup, send)

def found(~c: S.Configuration, selected: Maybe<&2, G.Entry>, before: E.Snapshot, handle: String, cleanup: CleanupReturn, send: V.SendReturn) -> InvalidationRun:
  match selected:
    case None{}: lift(V.error(S.Failure{}, before, send))
    case Some{entry}:
      fitting(R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})), before, handle, cleanup, send)

def proof_checked(~c: S.Configuration, empty: Bool, +before: E.Snapshot, +raw: P.Request, cleanup: CleanupReturn, send: V.SendReturn) -> InvalidationRun:
  match empty:
    case False{}: lift(V.error(S.Input{}, before, send))
    case True{}: found(c, G.lookup(E.instance(before), I.code(raw), E.registry(before)), before, I.code(raw), cleanup, send)

def authenticated(~c: S.Configuration, identity: Maybe<&2, D.Context>, before: E.Snapshot, +raw: P.Request, cleanup: CleanupReturn, send: V.SendReturn) -> InvalidationRun:
  match identity:
    case None{}: lift(V.error(S.Authentication{}, before, send))
    case Some{context}: proof_checked(c, String.eq(I.proof(raw), ""), before, raw, cleanup, send)

def run(~c: S.Configuration, +before: E.Snapshot, +raw: P.Request, cleanup: CleanupReturn, send: V.SendReturn) -> InvalidationRun:
  +identity = D.authenticate(E.database(before), I.credential(raw))
  push(InvalidationBase{V.WireReceived{W.Extension{W.Invalidate{}, raw}}},
    push(InvalidationBase{V.IdentityEstablished{W.Extension{W.Invalidate{}, raw}, identity}},
      authenticated(c, identity, before, raw, cleanup, send)))

def fact(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, event: InvalidationEvent) -> E.Fact:
  match event:
    case InvalidationBase{event}: V.fact(c, binding, public, event)
    case RegistryRemoved{handle, before, after}: E.Mutated{True{}, E.Invalidate{handle}, before, after}
