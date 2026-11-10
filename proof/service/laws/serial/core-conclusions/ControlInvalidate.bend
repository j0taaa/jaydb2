# All invalidation paths, including removal followed by pending/fatal/nonfatal
# cleanup, derive the same independent conclusion occurrence specification.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/PreparedRegistry.bend as G
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Requirements.bend as R
import ../../../../../contract/Resources.bend as X
import ../../../../../contract/Semantics.bend as S
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../phases/InvalidationPhases.bend as N
import ../../../model/EventObserver.bend as O
import ../../../model/serial/Common.bend as C
import ./Meaning.bend as M
import ./Algebra.bend as A
import ./ControlBase.bend as K

def pushed_events(+event: N.InvalidationEvent, run: N.InvalidationRun) ->
  {C.events(C.invalidation(N.push(event, run))) == Con{O.Invalidation{event}, C.events(C.invalidation(run))} : List<&2, O.AuditEvent>}:
  match run:
    case N.InvalidationRun{events, result, snapshot, waiting, closed}: {==}

def push(+event: N.InvalidationEvent, +run: N.InvalidationRun,
  none: {M.endpoint(O.Invalidation{event}) == None{} : Maybe<&2, M.Endpoint>}, shape: M.Shape<C.events(C.invalidation(run))>) ->
  M.Shape<C.events(C.invalidation(N.push(event, run)))>:
  %Equal.sym(List<&2, O.AuditEvent>, C.events(C.invalidation(N.push(event, run))), Con{O.Invalidation{event}, C.events(C.invalidation(run))}, pushed_events(event, run)) : M.Shape<_>
  A.prepend([O.Invalidation{event}], C.events(C.invalidation(run)),
    A.quiet_cons(O.Invalidation{event}, [],
      (%Equal.sym(Maybe<&2, M.Endpoint>, M.endpoint(O.Invalidation{event}), None{}, none) : {M.absent(_) == True{} : Bool} {==}), {==}), shape)

def cleaned(cleanup: N.CleanupReturn, +after: E.Snapshot, +bytes: List<&2, U32>, +send: V.SendReturn) ->
  M.Shape<C.events(C.invalidation(N.cleaned(cleanup, after, bytes, send)))>:
  match cleanup:
    case N.CleanupPending{}: K.pending(K.InvalidationEmbedding{}, after)
    case N.CleanupFailed{identifier, fatal}: K.failed(K.InvalidationEmbedding{}, X.Prepare{}, identifier, fatal, after, send)
    case N.CleanupComplete{}: K.receipt(K.InvalidationEmbedding{}, after, W.InvalidatedReceipt{}, N.metadata(after), after, bytes, send)

def remove_and_cleanup(+before: E.Snapshot, +handle: String, +bytes: List<&2, U32>, +cleanup: N.CleanupReturn, +send: V.SendReturn) ->
  M.Shape<C.events(C.invalidation(N.remove_and_cleanup(before, handle, bytes, cleanup, send)))>:
  push(N.RegistryRemoved{handle, before, N.removed(before, handle)}, N.cleaned(cleanup, N.removed(before, handle), bytes, send), {==}, cleaned(cleanup, N.removed(before, handle), bytes, send))

def framed(frame: Maybe<&2, List<&2, U32>>, +before: E.Snapshot, +handle: String, +cleanup: N.CleanupReturn, +send: V.SendReturn) ->
  M.Shape<C.events(C.invalidation(N.framed(frame, before, handle, cleanup, send)))>:
  match frame:
    case None{}: K.inconsistent(K.InvalidationEmbedding{}, before)
    case Some{+bytes}:
      push(N.InvalidationBase{V.ReceiptPrepared{W.InvalidatedReceipt{}, bytes}}, N.remove_and_cleanup(before, handle, bytes, cleanup, send), {==}, remove_and_cleanup(before, handle, bytes, cleanup, send))

def fitting(fits: Bool, +before: E.Snapshot, +handle: String, +cleanup: N.CleanupReturn, +send: V.SendReturn) ->
  M.Shape<C.events(C.invalidation(N.fitting(fits, before, handle, cleanup, send)))>:
  match fits:
    case False{}: K.error(K.InvalidationEmbedding{}, S.Limit{}, before, send)
    case True{}: framed(W.frame_receipt(W.InvalidatedReceipt{}), before, handle, cleanup, send)

def found(~c: S.Configuration, selected: Maybe<&2, G.Entry>, +before: E.Snapshot, +handle: String, +cleanup: N.CleanupReturn, +send: V.SendReturn) ->
  M.Shape<C.events(C.invalidation(N.found(c, selected, before, handle, cleanup, send)))>:
  match selected:
    case None{}: K.error(K.InvalidationEmbedding{}, S.Failure{}, before, send)
    case Some{entry}: fitting(R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})), before, handle, cleanup, send)

def proof_checked(~c: S.Configuration, empty: Bool, +before: E.Snapshot, +raw: P.Request, +cleanup: N.CleanupReturn, +send: V.SendReturn) ->
  M.Shape<C.events(C.invalidation(N.proof_checked(c, empty, before, raw, cleanup, send)))>:
  match empty:
    case False{}: K.error(K.InvalidationEmbedding{}, S.Input{}, before, send)
    case True{}: found(c, G.lookup(E.instance(before), I.code(raw), E.registry(before)), before, I.code(raw), cleanup, send)

def authenticated(~c: S.Configuration, identity: Maybe<&2, D.Context>, +before: E.Snapshot, +raw: P.Request, +cleanup: N.CleanupReturn, +send: V.SendReturn) ->
  M.Shape<C.events(C.invalidation(N.authenticated(c, identity, before, raw, cleanup, send)))>:
  match identity:
    case None{}: K.error(K.InvalidationEmbedding{}, S.Authentication{}, before, send)
    case Some{context}: proof_checked(c, String.eq(I.proof(raw), ""), before, raw, cleanup, send)

law actual_invalidation_derives_all_conclusion_occurrences_and_exact_prior_framing:
  for ~c: S.Configuration
  for +before: E.Snapshot
  for +raw: P.Request
  for +cleanup: N.CleanupReturn
  for +send: V.SendReturn
  M.Shape<C.events(C.invalidation(N.run(c, before, raw, cleanup, send)))>
def actual_invalidation_derives_all_conclusion_occurrences_and_exact_prior_framing(c, before, raw, cleanup, send):
  push(N.InvalidationBase{V.WireReceived{W.Extension{W.Invalidate{}, raw}}},
    N.push(N.InvalidationBase{V.IdentityEstablished{W.Extension{W.Invalidate{}, raw}, D.authenticate(E.database(before), I.credential(raw))}}, N.authenticated(c, D.authenticate(E.database(before), I.credential(raw)), before, raw, cleanup, send)), {==},
    push(N.InvalidationBase{V.IdentityEstablished{W.Extension{W.Invalidate{}, raw}, D.authenticate(E.database(before), I.credential(raw))}}, N.authenticated(c, D.authenticate(E.database(before), I.credential(raw)), before, raw, cleanup, send), {==},
      authenticated(c, D.authenticate(E.database(before), I.credential(raw)), before, raw, cleanup, send)))
