# Two actual reached queries preceding removal; no cleanup completion required.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/PreparedRegistry.bend as G
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Requirements.bend as R
import ../../../../../contract/Semantics.bend as S
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../phases/InvalidationPhases.bend as N
import ../../../phases/InvalidationEvents.bend as Original
import ../../../model/FrameBounds.bend as B

type Point is Data:
  Identity{}
  Receipt{}

def index(point: Point) -> Nat:
  match point:
    case Identity{}: 1n
    case Receipt{}: 2n

def value(point: Point, raw: P.Request, context: D.Context, bytes: List<&2, U32>) -> N.InvalidationEvent:
  match point:
    case Identity{}: N.InvalidationBase{V.IdentityEstablished{W.Extension{W.Invalidate{}, raw}, Some{context}}}
    case Receipt{}: N.InvalidationBase{V.ReceiptPrepared{W.InvalidatedReceipt{}, bytes}}

def prefix_query(+point: Point, +before: E.Snapshot, +raw: P.Request, +context: D.Context, +bytes: List<&2, U32>, tail: N.InvalidationRun) ->
  {B.query(N.InvalidationEvent, N.events(Original.removal_prefix(before, raw, context, bytes, tail)), index(point)) == Some{value(point, raw, context, bytes)} : Maybe<&2, N.InvalidationEvent>}:
  match point tail:
    case Identity{} N.InvalidationRun{events, result, snapshot, waiting, closed}: {==}
    case Receipt{} N.InvalidationRun{events, result, snapshot, waiting, closed}: {==}

def query(~c: S.Configuration, +point: Point, +before: E.Snapshot, +raw: P.Request, +context: D.Context, +entry: G.Entry, +bytes: List<&2, U32>, +cleanup: N.CleanupReturn, +send: V.SendReturn,
  auth: {D.authenticate(E.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
  empty: {String.eq(I.proof(raw), "") == True{} : Bool},
  lookup: {G.lookup(E.instance(before), I.code(raw), E.registry(before)) == Some{entry} : Maybe<&2, G.Entry>},
  fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})) == True{} : Bool},
  frame: {W.frame_receipt(W.InvalidatedReceipt{}) == Some{bytes} : Maybe<&2, List<&2, U32>>}) ->
  {B.query(N.InvalidationEvent, N.events(N.run(c, before, raw, cleanup, send)), index(point)) == Some{value(point, raw, context, bytes)} : Maybe<&2, N.InvalidationEvent>}:
  %Equal.sym(N.InvalidationRun, N.run(c, before, raw, cleanup, send), Original.removal_prefix(before, raw, context, bytes, N.cleaned(cleanup, N.removed(before, I.code(raw)), bytes, send)),
    Original.actual_authorized_framed_invalidation_has_its_exact_removal_phases(c, before, raw, entry, context, bytes, cleanup, send, auth, empty, lookup, fits, frame)) :
      {B.query(N.InvalidationEvent, N.events(_), index(point)) == Some{value(point, raw, context, bytes)} : Maybe<&2, N.InvalidationEvent>}
  prefix_query(point, before, raw, context, bytes, N.cleaned(cleanup, N.removed(before, I.code(raw)), bytes, send))
