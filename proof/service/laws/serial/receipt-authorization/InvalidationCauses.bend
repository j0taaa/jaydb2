# Every actual INVALIDATED receipt FRAME derives original auth/empty-proof/
# lookup/fit/frame DATA BEFORE removal, for EVERY later cleanup primitive.
# Cleanup completion and an eventual successful receipt are never premises.
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
import ../../../../Foundations.bend as F
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../phases/InvalidationPhases.bend as N
import ../../../model/FrameBounds.bend as B
import ./PreparationCauses.bend as Quiet

type Cause<-c: S.Configuration, -before: E.Snapshot, -raw: P.Request, -cleanup: N.CleanupReturn,
  -send: V.SendReturn, -event: V.PreparationEvent> is Data:
  Cause{context: D.Context, entry: G.Entry, bytes: List<&2, U32>,
    authenticated: {D.authenticate(E.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
    proof_empty: {String.eq(I.proof(raw), "") == True{} : Bool},
    found: {G.lookup(E.instance(before), I.code(raw), E.registry(before)) == Some{entry} : Maybe<&2, G.Entry>},
    fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})) == True{} : Bool},
    frame: {W.frame_receipt(W.InvalidatedReceipt{}) == Some{bytes} : Maybe<&2, List<&2, U32>>},
    payload: {event == V.ReceiptPrepared{W.InvalidatedReceipt{}, bytes} : V.PreparationEvent}}

def VClaim(-c: S.Configuration, -before: E.Snapshot, -raw: P.Request, -cleanup: N.CleanupReturn, -send: V.SendReturn, event: V.PreparationEvent) -> Type:
  match event:
    case V.ReceiptPrepared{receipt, bytes}: Cause<c, before, raw, cleanup, send, V.ReceiptPrepared{receipt, bytes}>
    case _: Unit

def VAll(-c: S.Configuration, -before: E.Snapshot, -raw: P.Request, -cleanup: N.CleanupReturn, -send: V.SendReturn, events: List<&2, V.PreparationEvent>) -> Type:
  match events:
    case Nil{}: Unit
    case Con{event, rest}: L.E<VClaim(c, before, raw, cleanup, send, event), VAll(c, before, raw, cleanup, send, rest)>

def Claim(-c: S.Configuration, -before: E.Snapshot, -raw: P.Request, -cleanup: N.CleanupReturn, -send: V.SendReturn, event: N.InvalidationEvent) -> Type:
  match event:
    case N.InvalidationBase{phase}: VClaim(c, before, raw, cleanup, send, phase)
    case N.RegistryRemoved{handle, before, after}: Unit

def All(-c: S.Configuration, -before: E.Snapshot, -raw: P.Request, -cleanup: N.CleanupReturn, -send: V.SendReturn, events: List<&2, N.InvalidationEvent>) -> Type:
  match events:
    case Nil{}: Unit
    case Con{event, rest}: L.E<Claim(c, before, raw, cleanup, send, event), All(c, before, raw, cleanup, send, rest)>

def no_receipt(-c: S.Configuration, -before: E.Snapshot, -raw: P.Request, -cleanup: N.CleanupReturn, -send: V.SendReturn,
  event: V.PreparationEvent, quiet: Quiet.Quiet(event)) -> VClaim(c, before, raw, cleanup, send, event):
  match event:
    case V.ReceiptConcluded{receipt, result, snapshot, closes}: Unit{}
    case V.WireReceived{wire}: Unit{}
    case V.IdentityEstablished{wire, context}: Unit{}
    case V.Accepted{wire, context}: Unit{}
    case V.Refuted{wire, context}: Unit{}
    case V.PrimitiveFailed{stage, identifier, fatal}: Unit{}
    case V.HandleChosen{handle}: Unit{}
    case V.ReceiptPrepared{receipt, bytes}: L.ex_false(VClaim(c, before, raw, cleanup, send, V.ReceiptPrepared{receipt, bytes}), quiet)
    case V.ArtifactSealed{entry}: Unit{}
    case V.RegistryChanged{entry, before, after}: Unit{}
    case V.ErrorPrepared{status, bytes}: Unit{}
    case V.ErrorConcluded{status, snapshot, closes}: Unit{}
    case V.Delivered{bytes}: Unit{}
    case V.Interrupted{prefix}: Unit{}
    case V.Closed{}: Unit{}

def quiet_events(-c: S.Configuration, -before: E.Snapshot, -raw: P.Request, -cleanup: N.CleanupReturn, -send: V.SendReturn,
  events: List<&2, V.PreparationEvent>, quiet: Quiet.AllQuiet(events)) -> VAll(c, before, raw, cleanup, send, events):
  match events quiet:
    case Nil{} unit: Unit{}
    case Con{event, rest} L.Both{head, later}:
      L.Both{no_receipt(c, before, raw, cleanup, send, event, head), quiet_events(c, before, raw, cleanup, send, rest, later)}

def base_events(-c: S.Configuration, -before: E.Snapshot, -raw: P.Request, -cleanup: N.CleanupReturn, -send: V.SendReturn,
  events: List<&2, V.PreparationEvent>, proofs: VAll(c, before, raw, cleanup, send, events)) -> All(c, before, raw, cleanup, send, N.base_events(events)):
  match events proofs:
    case Nil{} unit: Unit{}
    case Con{event, rest} L.Both{head, later}: L.Both{head, base_events(c, before, raw, cleanup, send, rest, later)}

def lift(-c: S.Configuration, -before: E.Snapshot, -raw: P.Request, -cleanup: N.CleanupReturn, -send: V.SendReturn,
  +run: V.PreparationRun, proofs: VAll(c, before, raw, cleanup, send, V.events(run))) -> All(c, before, raw, cleanup, send, N.events(N.lift(run))):
  match run:
    case V.PreparationRun{events, result, snapshot, waiting, closed}: base_events(c, before, raw, cleanup, send, events, proofs)

def lift_quiet(-c: S.Configuration, -before: E.Snapshot, -raw: P.Request, -cleanup: N.CleanupReturn, -send: V.SendReturn,
  +run: V.PreparationRun, quiet: Quiet.AllQuiet(V.events(run))) -> All(c, before, raw, cleanup, send, N.events(N.lift(run))):
  lift(c, before, raw, cleanup, send, run, quiet_events(c, before, raw, cleanup, send, V.events(run), quiet))

def vpush(-c: S.Configuration, -before: E.Snapshot, -raw: P.Request, -cleanup: N.CleanupReturn, -send: V.SendReturn,
  +event: V.PreparationEvent, +run: V.PreparationRun, head: VClaim(c, before, raw, cleanup, send, event), later: VAll(c, before, raw, cleanup, send, V.events(run))) ->
  VAll(c, before, raw, cleanup, send, V.events(V.push(event, run))):
  match run:
    case V.PreparationRun{events, result, snapshot, waiting, closed}: L.Both{head, later}

def push(-c: S.Configuration, -before: E.Snapshot, -raw: P.Request, -cleanup: N.CleanupReturn, -send: V.SendReturn,
  +event: N.InvalidationEvent, +run: N.InvalidationRun, head: Claim(c, before, raw, cleanup, send, event), later: All(c, before, raw, cleanup, send, N.events(run))) ->
  All(c, before, raw, cleanup, send, N.events(N.push(event, run))):
  match run:
    case N.InvalidationRun{events, result, snapshot, waiting, closed}: L.Both{head, later}

# Original input facts, constructed only on the reached authenticated lookup.
type Input<-before: E.Snapshot, -raw: P.Request> is Data:
  Input{context: D.Context, entry: G.Entry,
    authenticated: {D.authenticate(E.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
    proof_empty: {String.eq(I.proof(raw), "") == True{} : Bool},
    found: {G.lookup(E.instance(before), I.code(raw), E.registry(before)) == Some{entry} : Maybe<&2, G.Entry>}}

def cleaned(~c: S.Configuration, +before: E.Snapshot, +raw: P.Request, cleanup: N.CleanupReturn, +send: V.SendReturn, +bytes: List<&2, U32>) ->
  All(c, before, raw, cleanup, send, N.events(N.cleaned(cleanup, N.removed(before, I.code(raw)), bytes, send))):
  match cleanup:
    case N.CleanupPending{}: lift(c, before, raw, N.CleanupPending{}, send, V.pending(N.removed(before, I.code(raw))), Unit{})
    case N.CleanupFailed{+identifier, +fatal}:
      lift_quiet(c, before, raw, N.CleanupFailed{identifier, fatal}, send,
        V.failed(X.Prepare{}, identifier, fatal, N.removed(before, I.code(raw)), send), Quiet.quiet_failed(X.Prepare{}, identifier, fatal, N.removed(before, I.code(raw)), send))
    case N.CleanupComplete{}:
      lift_quiet(c, before, raw, N.CleanupComplete{}, send,
        V.push(V.ReceiptConcluded{W.InvalidatedReceipt{}, N.metadata(N.removed(before, I.code(raw))), N.removed(before, I.code(raw)), False{}}, V.delivery(send, bytes, N.metadata(N.removed(before, I.code(raw))), N.removed(before, I.code(raw)))),
        Quiet.quiet_prepend(V.ReceiptConcluded{W.InvalidatedReceipt{}, N.metadata(N.removed(before, I.code(raw))), N.removed(before, I.code(raw)), False{}}, V.delivery(send, bytes, N.metadata(N.removed(before, I.code(raw))), N.removed(before, I.code(raw))), Unit{},
          Quiet.quiet_delivery(send, bytes, N.metadata(N.removed(before, I.code(raw))), N.removed(before, I.code(raw)))))

def remove_and_cleanup(~c: S.Configuration, +before: E.Snapshot, +raw: P.Request, +cleanup: N.CleanupReturn, +send: V.SendReturn, +bytes: List<&2, U32>) ->
  All(c, before, raw, cleanup, send, N.events(N.remove_and_cleanup(before, I.code(raw), bytes, cleanup, send))):
  push(c, before, raw, cleanup, send, N.RegistryRemoved{I.code(raw), before, N.removed(before, I.code(raw))},
    N.cleaned(cleanup, N.removed(before, I.code(raw)), bytes, send), Unit{}, cleaned(c, before, raw, cleanup, send, bytes))

def prepared(~c: S.Configuration, +before: E.Snapshot, +raw: P.Request, +cleanup: N.CleanupReturn, +send: V.SendReturn, +bytes: List<&2, U32>, input: Input<before, raw>,
  fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})) == True{} : Bool},
  actual: {W.frame_receipt(W.InvalidatedReceipt{}) == Some{bytes} : Maybe<&2, List<&2, U32>>}) ->
  All(c, before, raw, cleanup, send, N.events(N.push(N.InvalidationBase{V.ReceiptPrepared{W.InvalidatedReceipt{}, bytes}}, N.remove_and_cleanup(before, I.code(raw), bytes, cleanup, send)))):
  match input:
    case Input{context, entry, authenticated, empty, found}:
      push(c, before, raw, cleanup, send, N.InvalidationBase{V.ReceiptPrepared{W.InvalidatedReceipt{}, bytes}}, N.remove_and_cleanup(before, I.code(raw), bytes, cleanup, send),
        Cause{context, entry, bytes, authenticated, empty, found, fits, actual, {==}}, remove_and_cleanup(c, before, raw, cleanup, send, bytes))

def framed(~c: S.Configuration, frame: Maybe<&2, List<&2, U32>>, +before: E.Snapshot, +raw: P.Request, +cleanup: N.CleanupReturn, +send: V.SendReturn,
  input: Input<before, raw>,
  fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})) == True{} : Bool},
  actual: {W.frame_receipt(W.InvalidatedReceipt{}) == frame : Maybe<&2, List<&2, U32>>}) ->
  All(c, before, raw, cleanup, send, N.events(N.framed(frame, before, I.code(raw), cleanup, send))):
  match frame:
    case None{}: lift(c, before, raw, cleanup, send, V.inconsistent(before), Unit{})
    case Some{+bytes}:
      prepared(c, before, raw, cleanup, send, bytes, input, fits, actual)

def fitting(~c: S.Configuration, fits: Bool, +before: E.Snapshot, +raw: P.Request, +cleanup: N.CleanupReturn, +send: V.SendReturn,
  input: Input<before, raw>, actual: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})) == fits : Bool}) ->
  All(c, before, raw, cleanup, send, N.events(N.fitting(fits, before, I.code(raw), cleanup, send))):
  match fits:
    case False{}:
      lift_quiet(c, before, raw, cleanup, send, V.error(S.Limit{}, before, send), Quiet.quiet_error(S.Limit{}, before, send))
    case True{}: framed(c, W.frame_receipt(W.InvalidatedReceipt{}), before, raw, cleanup, send, input, actual, {==})

def found(~c: S.Configuration, selected: Maybe<&2, G.Entry>, +before: E.Snapshot, +raw: P.Request, +cleanup: N.CleanupReturn, +send: V.SendReturn,
  +context: D.Context,
  authenticated: {D.authenticate(E.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
  proof_empty: {String.eq(I.proof(raw), "") == True{} : Bool},
  actual: {G.lookup(E.instance(before), I.code(raw), E.registry(before)) == selected : Maybe<&2, G.Entry>}) ->
  All(c, before, raw, cleanup, send, N.events(N.found(c, selected, before, I.code(raw), cleanup, send))):
  match selected:
    case None{}: lift_quiet(c, before, raw, cleanup, send, V.error(S.Failure{}, before, send), Quiet.quiet_error(S.Failure{}, before, send))
    case Some{entry}:
      fitting(c, R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})), before, raw, cleanup, send,
        Input{context, entry, authenticated, proof_empty, actual}, {==})

def proof_checked(~c: S.Configuration, empty: Bool, +before: E.Snapshot, +raw: P.Request, +cleanup: N.CleanupReturn, +send: V.SendReturn,
  +context: D.Context,
  authenticated: {D.authenticate(E.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
  actual: {String.eq(I.proof(raw), "") == empty : Bool}) ->
  All(c, before, raw, cleanup, send, N.events(N.proof_checked(c, empty, before, raw, cleanup, send))):
  match empty:
    case False{}: lift_quiet(c, before, raw, cleanup, send, V.error(S.Input{}, before, send), Quiet.quiet_error(S.Input{}, before, send))
    case True{}: found(c, G.lookup(E.instance(before), I.code(raw), E.registry(before)), before, raw, cleanup, send, context, authenticated, actual, {==})

def authenticated(~c: S.Configuration, identity: Maybe<&2, D.Context>, +before: E.Snapshot, +raw: P.Request, +cleanup: N.CleanupReturn, +send: V.SendReturn,
  actual: {D.authenticate(E.database(before), I.credential(raw)) == identity : Maybe<&2, D.Context>}) ->
  All(c, before, raw, cleanup, send, N.events(N.authenticated(c, identity, before, raw, cleanup, send))):
  match identity:
    case None{}: lift_quiet(c, before, raw, cleanup, send, V.error(S.Authentication{}, before, send), Quiet.quiet_error(S.Authentication{}, before, send))
    case Some{+context}: proof_checked(c, String.eq(I.proof(raw), ""), before, raw, cleanup, send, context, actual, {==})

law every_actual_invalidation_receipt_frame_derives_original_authentication_and_lookup_before_every_cleanup_return:
  for ~c: S.Configuration
  for +before: E.Snapshot
  for +raw: P.Request
  for +cleanup: N.CleanupReturn
  for +send: V.SendReturn
  All(c, before, raw, cleanup, send, N.events(N.run(c, before, raw, cleanup, send)))
def every_actual_invalidation_receipt_frame_derives_original_authentication_and_lookup_before_every_cleanup_return(c, before, raw, cleanup, send):
  push(c, before, raw, cleanup, send, N.InvalidationBase{V.WireReceived{W.Extension{W.Invalidate{}, raw}}},
    N.push(N.InvalidationBase{V.IdentityEstablished{W.Extension{W.Invalidate{}, raw}, D.authenticate(E.database(before), I.credential(raw))}},
      N.authenticated(c, D.authenticate(E.database(before), I.credential(raw)), before, raw, cleanup, send)), Unit{},
    push(c, before, raw, cleanup, send, N.InvalidationBase{V.IdentityEstablished{W.Extension{W.Invalidate{}, raw}, D.authenticate(E.database(before), I.credential(raw))}},
      N.authenticated(c, D.authenticate(E.database(before), I.credential(raw)), before, raw, cleanup, send), Unit{},
      authenticated(c, D.authenticate(E.database(before), I.credential(raw)), before, raw, cleanup, send, {==})))

def query(~c: S.Configuration, +before: E.Snapshot, +raw: P.Request, +cleanup: N.CleanupReturn, +send: V.SendReturn,
  +events: List<&2, N.InvalidationEvent>, index: Nat, +event: N.InvalidationEvent, all: All(c, before, raw, cleanup, send, events),
  found: {B.query(N.InvalidationEvent, events, index) == Some{event} : Maybe<&2, N.InvalidationEvent>}) -> Claim(c, before, raw, cleanup, send, event):
  match events index all:
    case Nil{} _ unit: L.ex_false(Claim(c, before, raw, cleanup, send, event), F.none_negative_some(N.InvalidationEvent, event, found))
    case Con{+head, rest} Zero{} L.Both{claim, later}:
      %F.some_injective(N.InvalidationEvent, head, event, found) : Claim(c, before, raw, cleanup, send, _)
      claim
    case Con{head, +rest} Succ{prior} L.Both{claim, later}: query(c, before, raw, cleanup, send, rest, prior, event, later, found)

law any_actual_queried_invalidation_receipt_frame_recovers_its_original_guards_without_cleanup_completion:
  for ~c: S.Configuration
  for +before: E.Snapshot
  for +raw: P.Request
  for +cleanup: N.CleanupReturn
  for +send: V.SendReturn
  for +index: Nat
  for +receipt: W.Receipt
  for +bytes: List<&2, U32>
  for found: {B.query(N.InvalidationEvent, N.events(N.run(c, before, raw, cleanup, send)), index) == Some{N.InvalidationBase{V.ReceiptPrepared{receipt, bytes}}} : Maybe<&2, N.InvalidationEvent>}
  Cause<c, before, raw, cleanup, send, V.ReceiptPrepared{receipt, bytes}>
def any_actual_queried_invalidation_receipt_frame_recovers_its_original_guards_without_cleanup_completion(c, before, raw, cleanup, send, index, receipt, bytes, found):
  query(c, before, raw, cleanup, send, N.events(N.run(c, before, raw, cleanup, send)), index, N.InvalidationBase{V.ReceiptPrepared{receipt, bytes}},
    every_actual_invalidation_receipt_frame_derives_original_authentication_and_lookup_before_every_cleanup_return(c, before, raw, cleanup, send), found)
