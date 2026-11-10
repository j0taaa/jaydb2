# Exact removal queries include incomplete/fatal cleanup paths; mutation history
# does not depend on eventual successful conclusion or delivery.
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
import ../specification/ServiceLaws.bend as E
import ../model/FrameBounds.bend as B
import ./PreparePhases.bend as V
import ./PrepareFailures.bend as Failures
import ./InvalidationPhases.bend as N

def selected_exact(~c: S.Configuration, +before: E.Snapshot, +raw: P.Request, +entry: G.Entry,
  +bytes: List<&2, U32>, +cleanup: N.CleanupReturn, +send: V.SendReturn,
  present: {G.lookup(E.instance(before), I.code(raw), E.registry(before)) == Some{entry} : Maybe<&2, G.Entry>},
  fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})) == True{} : Bool},
  frame: {W.frame_receipt(W.InvalidatedReceipt{}) == Some{bytes} : Maybe<&2, List<&2, U32>>}) ->
  {N.proof_checked(c, True{}, before, raw, cleanup, send) ==
    N.push(N.InvalidationBase{V.ReceiptPrepared{W.InvalidatedReceipt{}, bytes}},
      N.remove_and_cleanup(before, I.code(raw), bytes, cleanup, send)) : N.InvalidationRun}:
  %Equal.sym(Maybe<&2, G.Entry>, G.lookup(E.instance(before), I.code(raw), E.registry(before)), Some{entry}, present) :
    {N.found(c, _, before, I.code(raw), cleanup, send) ==
      N.push(N.InvalidationBase{V.ReceiptPrepared{W.InvalidatedReceipt{}, bytes}}, N.remove_and_cleanup(before, I.code(raw), bytes, cleanup, send)) : N.InvalidationRun}
  %Equal.sym(Bool, R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})), True{}, fits) :
    {N.fitting(_, before, I.code(raw), cleanup, send) ==
      N.push(N.InvalidationBase{V.ReceiptPrepared{W.InvalidatedReceipt{}, bytes}}, N.remove_and_cleanup(before, I.code(raw), bytes, cleanup, send)) : N.InvalidationRun}
  %Equal.sym(Maybe<&2, List<&2, U32>>, W.frame_receipt(W.InvalidatedReceipt{}), Some{bytes}, frame) :
    {N.framed(_, before, I.code(raw), cleanup, send) ==
      N.push(N.InvalidationBase{V.ReceiptPrepared{W.InvalidatedReceipt{}, bytes}}, N.remove_and_cleanup(before, I.code(raw), bytes, cleanup, send)) : N.InvalidationRun}
  {==}

def after_auth_exact(~c: S.Configuration, +before: E.Snapshot, +raw: P.Request, +entry: G.Entry,
  +context: D.Context, +bytes: List<&2, U32>, +cleanup: N.CleanupReturn, +send: V.SendReturn,
  empty: {String.eq(I.proof(raw), "") == True{} : Bool},
  present: {G.lookup(E.instance(before), I.code(raw), E.registry(before)) == Some{entry} : Maybe<&2, G.Entry>},
  fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})) == True{} : Bool},
  frame: {W.frame_receipt(W.InvalidatedReceipt{}) == Some{bytes} : Maybe<&2, List<&2, U32>>}) ->
  {N.authenticated(c, Some{context}, before, raw, cleanup, send) ==
    N.push(N.InvalidationBase{V.ReceiptPrepared{W.InvalidatedReceipt{}, bytes}},
      N.remove_and_cleanup(before, I.code(raw), bytes, cleanup, send)) : N.InvalidationRun}:
  %Equal.sym(Bool, String.eq(I.proof(raw), ""), True{}, empty) :
    {N.proof_checked(c, _, before, raw, cleanup, send) ==
      N.push(N.InvalidationBase{V.ReceiptPrepared{W.InvalidatedReceipt{}, bytes}}, N.remove_and_cleanup(before, I.code(raw), bytes, cleanup, send)) : N.InvalidationRun}
  selected_exact(c, before, raw, entry, bytes, cleanup, send, present, fits, frame)

def removal_prefix(+before: E.Snapshot, +raw: P.Request, context: D.Context, bytes: List<&2, U32>, tail: N.InvalidationRun) -> N.InvalidationRun:
  N.push(N.InvalidationBase{V.WireReceived{W.Extension{W.Invalidate{}, raw}}},
    N.push(N.InvalidationBase{V.IdentityEstablished{W.Extension{W.Invalidate{}, raw}, Some{context}}},
      N.push(N.InvalidationBase{V.ReceiptPrepared{W.InvalidatedReceipt{}, bytes}},
        N.push(N.RegistryRemoved{I.code(raw), before, N.removed(before, I.code(raw))}, tail))))

def removal_prefix_query(+before: E.Snapshot, +raw: P.Request, +context: D.Context, +bytes: List<&2, U32>, tail: N.InvalidationRun) ->
  {B.query(N.InvalidationEvent, N.events(removal_prefix(before, raw, context, bytes, tail)), 3n) ==
    Some{N.RegistryRemoved{I.code(raw), before, N.removed(before, I.code(raw))}} : Maybe<&2, N.InvalidationEvent>}:
  match tail:
    case N.InvalidationRun{events, result, snapshot, waiting, closed}: {==}

law actual_authorized_framed_invalidation_has_its_exact_removal_phases:
  for ~c: S.Configuration
  for +before: E.Snapshot
  for +raw: P.Request
  for +entry: G.Entry
  for +context: D.Context
  for +bytes: List<&2, U32>
  for +cleanup: N.CleanupReturn
  for +send: V.SendReturn
  for authenticated: {D.authenticate(E.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>}
  for empty: {String.eq(I.proof(raw), "") == True{} : Bool}
  for present: {G.lookup(E.instance(before), I.code(raw), E.registry(before)) == Some{entry} : Maybe<&2, G.Entry>}
  for fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})) == True{} : Bool}
  for frame: {W.frame_receipt(W.InvalidatedReceipt{}) == Some{bytes} : Maybe<&2, List<&2, U32>>}
  {N.run(c, before, raw, cleanup, send) == removal_prefix(before, raw, context, bytes,
    N.cleaned(cleanup, N.removed(before, I.code(raw)), bytes, send)) : N.InvalidationRun}
def actual_authorized_framed_invalidation_has_its_exact_removal_phases(c, before, raw, entry, context, bytes, cleanup, send,
  authenticated, empty, present, fits, frame):
  %Equal.sym(Maybe<&2, D.Context>, D.authenticate(E.database(before), I.credential(raw)), Some{context}, authenticated) :
    {N.push(N.InvalidationBase{V.WireReceived{W.Extension{W.Invalidate{}, raw}}},
      N.push(N.InvalidationBase{V.IdentityEstablished{W.Extension{W.Invalidate{}, raw}, _}},
        N.authenticated(c, _, before, raw, cleanup, send))) ==
      removal_prefix(before, raw, context, bytes, N.cleaned(cleanup, N.removed(before, I.code(raw)), bytes, send)) : N.InvalidationRun}
  Equal.cong(N.InvalidationRun, N.InvalidationRun,
    tail => N.push(N.InvalidationBase{V.WireReceived{W.Extension{W.Invalidate{}, raw}}},
      N.push(N.InvalidationBase{V.IdentityEstablished{W.Extension{W.Invalidate{}, raw}, Some{context}}}, tail)),
    N.authenticated(c, Some{context}, before, raw, cleanup, send),
    N.push(N.InvalidationBase{V.ReceiptPrepared{W.InvalidatedReceipt{}, bytes}}, N.remove_and_cleanup(before, I.code(raw), bytes, cleanup, send)),
    after_auth_exact(c, before, raw, entry, context, bytes, cleanup, send, empty, present, fits, frame))

law actual_invalidation_supplies_the_exact_removal_query_before_any_cleanup_result:
  for ~c: S.Configuration
  for +before: E.Snapshot
  for +raw: P.Request
  for +entry: G.Entry
  for +context: D.Context
  for +bytes: List<&2, U32>
  for +cleanup: N.CleanupReturn
  for +send: V.SendReturn
  for authenticated: {D.authenticate(E.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>}
  for empty: {String.eq(I.proof(raw), "") == True{} : Bool}
  for present: {G.lookup(E.instance(before), I.code(raw), E.registry(before)) == Some{entry} : Maybe<&2, G.Entry>}
  for fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})) == True{} : Bool}
  for frame: {W.frame_receipt(W.InvalidatedReceipt{}) == Some{bytes} : Maybe<&2, List<&2, U32>>}
  {B.query(N.InvalidationEvent, N.events(N.run(c, before, raw, cleanup, send)), 3n) ==
    Some{N.RegistryRemoved{I.code(raw), before, N.removed(before, I.code(raw))}} : Maybe<&2, N.InvalidationEvent>}
def actual_invalidation_supplies_the_exact_removal_query_before_any_cleanup_result(c, before, raw, entry, context, bytes,
  cleanup, send, authenticated, empty, present, fits, frame):
  Equal.trans(Maybe<&2, N.InvalidationEvent>,
    B.query(N.InvalidationEvent, N.events(N.run(c, before, raw, cleanup, send)), 3n),
    B.query(N.InvalidationEvent, N.events(removal_prefix(before, raw, context, bytes,
      N.cleaned(cleanup, N.removed(before, I.code(raw)), bytes, send))), 3n),
    Some{N.RegistryRemoved{I.code(raw), before, N.removed(before, I.code(raw))}},
    Equal.cong(N.InvalidationRun, Maybe<&2, N.InvalidationEvent>, run => B.query(N.InvalidationEvent, N.events(run), 3n),
      N.run(c, before, raw, cleanup, send), removal_prefix(before, raw, context, bytes,
        N.cleaned(cleanup, N.removed(before, I.code(raw)), bytes, send)),
      actual_authorized_framed_invalidation_has_its_exact_removal_phases(c, before, raw, entry, context, bytes,
        cleanup, send, authenticated, empty, present, fits, frame)),
    removal_prefix_query(before, raw, context, bytes, N.cleaned(cleanup, N.removed(before, I.code(raw)), bytes, send)))

law pending_cleanup_has_an_actual_removal_and_no_completed_result:
  for +before: E.Snapshot
  for +handle: String
  for bytes: List<&2, U32>
  for send: V.SendReturn
  L.E<{B.query(N.InvalidationEvent, N.events(N.remove_and_cleanup(before, handle, bytes, N.CleanupPending{}, send)), 0n) ==
      Some{N.RegistryRemoved{handle, before, N.removed(before, handle)}} : Maybe<&2, N.InvalidationEvent>},
    L.E<{N.snapshot(N.remove_and_cleanup(before, handle, bytes, N.CleanupPending{}, send)) == N.removed(before, handle) : E.Snapshot},
      {N.result(N.remove_and_cleanup(before, handle, bytes, N.CleanupPending{}, send)) == None{} : Maybe<&2, H.ControlResult>}>>
def pending_cleanup_has_an_actual_removal_and_no_completed_result(before, handle, bytes, send):
  L.Both{{==}, L.Both{{==}, {==}}}

law lifted_snapshot_is_the_original_complete_snapshot:
  for +run: V.PreparationRun
  {N.snapshot(N.lift(run)) == V.snapshot(run) : E.Snapshot}
def lifted_snapshot_is_the_original_complete_snapshot(run):
  match run:
    case V.PreparationRun{events, result, snapshot, waiting, closed}: {==}

law every_cleanup_return_retains_the_already_removed_snapshot:
  for cleanup: N.CleanupReturn
  for +after: E.Snapshot
  for +bytes: List<&2, U32>
  for +send: V.SendReturn
  {N.snapshot(N.cleaned(cleanup, after, bytes, send)) == after : E.Snapshot}
def every_cleanup_return_retains_the_already_removed_snapshot(cleanup, after, bytes, send):
  match cleanup:
    case N.CleanupPending{}: {==}
    case N.CleanupComplete{}:
      match send:
        case V.SendPending{}: {==}
        case V.SendComplete{}: {==}
        case V.SendInterrupted{prefix}: {==}
    case N.CleanupFailed{+identifier, +fatal}:
      Equal.trans(E.Snapshot, N.snapshot(N.lift(V.failed(X.Prepare{}, identifier, fatal, after, send))),
        V.snapshot(V.failed(X.Prepare{}, identifier, fatal, after, send)), after,
        lifted_snapshot_is_the_original_complete_snapshot(V.failed(X.Prepare{}, identifier, fatal, after, send)),
        Failures.a_real_primitive_failure_preserves_the_complete_snapshot(X.Prepare{}, identifier, fatal, after, send))
