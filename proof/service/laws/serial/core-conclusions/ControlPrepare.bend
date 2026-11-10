# Every actual preparation branch has zero or one conclusion, and every
# transaction conclusion has its own earlier matching prepared frame. No
# checker/certificate/allocator/cleanup/output correctness premise is needed.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/PreparedLaws.bend as H
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/PreparedRegistry.bend as G
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Requirements.bend as R
import ../../../../../contract/Semantics.bend as S
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ./Meaning.bend as M
import ./ControlBase.bend as K

def register_result(+kind: K.Embedding, completed: H.ControlResult, +before: E.Snapshot, +entry: G.Entry, +bytes: List<&2, U32>, +send: V.SendReturn) ->
  M.Shape<K.events(kind, V.register_result(completed, before, entry, bytes, send))>:
  match completed:
    case H.ControlResult{+state, +entries, H.Metadata{+receipt}}:
      +actual: H.ControlResult = H.ControlResult{state, entries, H.Metadata{receipt}}
      +after: E.Snapshot = V.registered_snapshot(before, actual)
      K.push(kind, V.RegistryChanged{entry, before, after}, V.push(V.ReceiptConcluded{receipt, actual, after, False{}}, V.delivery(send, bytes, actual, after)), {==},
        K.receipt(kind, before, receipt, actual, after, bytes, send))
    case H.ControlResult{state, entries, H.Error{+status}}: K.error(kind, status, before, send)

def seal_result(~c: S.Configuration, +kind: K.Embedding, seal: V.SealReturn, +mode: V.Mode, +raw: P.Request,
  +before: E.Snapshot, +handle: String, +bytes: List<&2, U32>, +send: V.SendReturn) ->
  M.Shape<K.events(kind, V.seal_result(c, seal, mode, raw, before, handle, bytes, send))>:
  match seal:
    case V.SealPending{}: K.pending(kind, before)
    case V.SealFailed{stage, identifier, fatal}: K.failed(kind, stage, identifier, fatal, before, send)
    case V.SealSucceeded{seal}:
      +entry: G.Entry = V.entry(mode, raw, E.instance(before), handle, seal)
      K.push(kind, V.ArtifactSealed{entry}, V.register_result(H.register(c, E.database(before), E.instance(before), entry, E.registry(before)), before, entry, bytes, send), {==},
        register_result(kind, H.register(c, E.database(before), E.instance(before), entry, E.registry(before)), before, entry, bytes, send))

def fitting_frame(~c: S.Configuration, +kind: K.Embedding, frame: Maybe<&2, List<&2, U32>>, +mode: V.Mode, +raw: P.Request,
  +before: E.Snapshot, +handle: String, +seal: V.SealReturn, +send: V.SendReturn) ->
  M.Shape<K.events(kind, V.fitting_frame(c, frame, mode, raw, before, handle, seal, send))>:
  match frame:
    case None{}: K.inconsistent(kind, before)
    case Some{+bytes}:
      K.push(kind, V.ReceiptPrepared{W.PreparedReceipt{handle}, bytes}, V.seal_result(c, seal, mode, raw, before, handle, bytes, send), {==},
        seal_result(c, kind, seal, mode, raw, before, handle, bytes, send))

def receipt_fit(~c: S.Configuration, +kind: K.Embedding, fits: Bool, +mode: V.Mode, +raw: P.Request,
  +before: E.Snapshot, +handle: String, +seal: V.SealReturn, +send: V.SendReturn) ->
  M.Shape<K.events(kind, V.receipt_fit(c, fits, mode, raw, before, handle, seal, send))>:
  match fits:
    case False{}: K.error(kind, S.Limit{}, before, send)
    case True{}: fitting_frame(c, kind, W.frame_receipt(W.PreparedReceipt{handle}), mode, raw, before, handle, seal, send)

def allocated(~c: S.Configuration, +kind: K.Embedding, allocation: V.AllocatorReturn, +mode: V.Mode, +raw: P.Request,
  +before: E.Snapshot, +seal: V.SealReturn, +send: V.SendReturn) ->
  M.Shape<K.events(kind, V.allocated(c, allocation, mode, raw, before, seal, send))>:
  match allocation:
    case V.AllocatorPending{}: K.pending(kind, before)
    case V.AllocatorFailed{stage, identifier, fatal}: K.failed(kind, stage, identifier, fatal, before, send)
    case V.AllocatorChosen{+handle}:
      K.push(kind, V.HandleChosen{handle}, V.receipt_fit(c, R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})), mode, raw, before, handle, seal, send), {==},
        receipt_fit(c, kind, R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})), mode, raw, before, handle, seal, send))

def checked(~c: S.Configuration, +kind: K.Embedding, check: V.CheckerReturn, +mode: V.Mode, +raw: P.Request, +context: D.Context,
  +before: E.Snapshot, +allocation: V.AllocatorReturn, +seal: V.SealReturn, +send: V.SendReturn) ->
  M.Shape<K.events(kind, V.checked(c, check, mode, raw, context, before, allocation, seal, send))>:
  match check:
    case V.CheckerPending{}: K.pending(kind, before)
    case V.CheckerFailed{stage, identifier, fatal}: K.failed(kind, stage, identifier, fatal, before, send)
    case V.CheckerRefuted{}:
      K.push(kind, V.Refuted{W.Extension{V.operation(mode), raw}, context}, V.error(S.Certificate{}, before, send), {==}, K.error(kind, S.Certificate{}, before, send))
    case V.CheckerAccepted{}:
      K.push(kind, V.Accepted{W.Extension{V.operation(mode), raw}, context}, V.allocated(c, allocation, mode, raw, before, seal, send), {==}, allocated(c, kind, allocation, mode, raw, before, seal, send))

def authenticated_returns(~c: S.Configuration, +kind: K.Embedding, +mode: V.Mode, +raw: P.Request, +before: E.Snapshot, +context: D.Context,
  returns: V.Returns) -> M.Shape<K.events(kind, V.authenticated(c, Some{context}, mode, raw, before, returns))>:
  match returns:
    case V.Returns{check, allocation, seal, send}: checked(c, kind, check, mode, raw, context, before, allocation, seal, send)

def authenticated(~c: S.Configuration, +kind: K.Embedding, identity: Maybe<&2, D.Context>, +mode: V.Mode, +raw: P.Request,
  +before: E.Snapshot, +returns: V.Returns) -> M.Shape<K.events(kind, V.authenticated(c, identity, mode, raw, before, returns))>:
  match identity:
    case None{}: K.error(kind, S.Authentication{}, before, V.send_of(returns))
    case Some{context}:
      authenticated_returns(c, kind, mode, raw, before, context, returns)

law actual_preparation_derives_all_conclusion_occurrences_and_exact_prior_framing:
  for ~c: S.Configuration
  for +kind: K.Embedding
  for +mode: V.Mode
  for +raw: P.Request
  for +before: E.Snapshot
  for +returns: V.Returns
  M.Shape<K.events(kind, V.run(c, mode, raw, before, returns))>
def actual_preparation_derives_all_conclusion_occurrences_and_exact_prior_framing(c, kind, mode, raw, before, returns):
  K.push(kind, V.WireReceived{W.Extension{V.operation(mode), raw}},
    V.push(V.IdentityEstablished{W.Extension{V.operation(mode), raw}, D.authenticate(E.database(before), I.credential(raw))}, V.authenticated(c, D.authenticate(E.database(before), I.credential(raw)), mode, raw, before, returns)), {==},
    K.push(kind, V.IdentityEstablished{W.Extension{V.operation(mode), raw}, D.authenticate(E.database(before), I.credential(raw))}, V.authenticated(c, D.authenticate(E.database(before), I.credential(raw)), mode, raw, before, returns), {==},
      authenticated(c, kind, D.authenticate(E.database(before), I.credential(raw)), mode, raw, before, returns)))
