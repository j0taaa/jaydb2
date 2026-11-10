# Exact receipt-preparation prefix BEFORE arbitrary seal/registration outcomes.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Requirements.bend as R
import ../../../../../contract/Semantics.bend as S
import ../../../../Foundations.bend as F
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../model/FrameBounds.bend as B
import ../../../model/PreparationPrefix.bend as Header
import ./PreparationCauses.bend as Cause

def wrapped(+mode: V.Mode, +raw: P.Request, +context: D.Context, +handle: String, bytes: List<&2, U32>, last: V.PreparationRun) -> V.PreparationRun:
  Header.header(mode, raw, Some{context}, V.push(V.Accepted{W.Extension{V.operation(mode), raw}, context}, V.push(V.HandleChosen{handle}, V.push(V.ReceiptPrepared{W.PreparedReceipt{handle}, bytes}, last))))

def actual(~c: S.Configuration, +mode: V.Mode, +raw: P.Request, +before: E.Snapshot, +context: D.Context, +handle: String, +seal: V.SealReturn, +bytes: List<&2, U32>, +send: V.SendReturn,
  auth: {D.authenticate(E.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
  fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})) == True{} : Bool},
  frame: {W.frame_receipt(W.PreparedReceipt{handle}) == Some{bytes} : Maybe<&2, List<&2, U32>>}) ->
  {V.run(c, mode, raw, before, V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, seal, send}) == wrapped(mode, raw, context, handle, bytes, V.seal_result(c, seal, mode, raw, before, handle, bytes, send)) : V.PreparationRun}:
  %Equal.sym(Maybe<&2, D.Context>, D.authenticate(E.database(before), I.credential(raw)), Some{context}, auth) :
    {Header.header(mode, raw, _, V.authenticated(c, _, mode, raw, before, V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, seal, send})) == wrapped(mode, raw, context, handle, bytes, V.seal_result(c, seal, mode, raw, before, handle, bytes, send)) : V.PreparationRun}
  %Equal.sym(Bool, R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})), True{}, fits) :
    {Header.header(mode, raw, Some{context}, V.push(V.Accepted{W.Extension{V.operation(mode), raw}, context}, V.push(V.HandleChosen{handle}, V.receipt_fit(c, _, mode, raw, before, handle, seal, send)))) == wrapped(mode, raw, context, handle, bytes, V.seal_result(c, seal, mode, raw, before, handle, bytes, send)) : V.PreparationRun}
  %Equal.sym(Maybe<&2, List<&2, U32>>, W.frame_receipt(W.PreparedReceipt{handle}), Some{bytes}, frame) :
    {Header.header(mode, raw, Some{context}, V.push(V.Accepted{W.Extension{V.operation(mode), raw}, context}, V.push(V.HandleChosen{handle}, V.fitting_frame(c, _, mode, raw, before, handle, seal, send)))) == wrapped(mode, raw, context, handle, bytes, V.seal_result(c, seal, mode, raw, before, handle, bytes, send)) : V.PreparationRun}
  {==}

def prefix(+mode: V.Mode, +raw: P.Request, +context: D.Context, handle: String) -> List<&2, V.PreparationEvent>:
  [V.WireReceived{W.Extension{V.operation(mode), raw}}, V.IdentityEstablished{W.Extension{V.operation(mode), raw}, Some{context}}, V.Accepted{W.Extension{V.operation(mode), raw}, context}, V.HandleChosen{handle}]

def prefix_quiet(mode: V.Mode, raw: P.Request, +context: D.Context, handle: String) -> Cause.AllQuiet(prefix(mode, raw, context, handle)):
  L.Both{Unit{}, L.Both{Unit{}, L.Both{Unit{}, L.Both{Unit{}, Unit{}}}}}

def append(first: List<&2, V.PreparationEvent>, last: List<&2, V.PreparationEvent>) -> List<&2, V.PreparationEvent>:
  match first:
    case Nil{}: last
    case Con{head, rest}: Con{head, append(rest, last)}

def quiet_query(+events: List<&2, V.PreparationEvent>, index: Nat, +event: V.PreparationEvent,
  quiet: Cause.AllQuiet(events), found: {B.query(V.PreparationEvent, events, index) == Some{event} : Maybe<&2, V.PreparationEvent>}) -> Cause.Quiet(event):
  match events index quiet:
    case Nil{} _ unit: L.ex_false(Cause.Quiet(event), F.none_negative_some(V.PreparationEvent, event, found))
    case Con{+head, rest} Zero{} L.Both{one, later}: %F.some_injective(V.PreparationEvent, head, event, found) : Cause.Quiet(_) one
    case Con{head, +rest} Succ{prior} L.Both{one, later}: quiet_query(rest, prior, event, later, found)

def quiet_not_prepared(+event: V.PreparationEvent, +receipt: W.Receipt, +bytes: List<&2, U32>, quiet: Cause.Quiet(event), same: {event == V.ReceiptPrepared{receipt, bytes} : V.PreparationEvent}) -> Empty:
  %same : Cause.Quiet(_) quiet

def only(+early: List<&2, V.PreparationEvent>, +tail: List<&2, V.PreparationEvent>, +handle: String, +prepared: List<&2, U32>, +receipt: W.Receipt, +bytes: List<&2, U32>, index: Nat,
  prefix_quiet: Cause.AllQuiet(early), suffix_quiet: Cause.AllQuiet(tail),
  found: {B.query(V.PreparationEvent, append(early, Con{V.ReceiptPrepared{W.PreparedReceipt{handle}, prepared}, tail}), index) == Some{V.ReceiptPrepared{receipt, bytes}} : Maybe<&2, V.PreparationEvent>}) -> {index == B.count(V.PreparationEvent, early) : Nat}:
  match early index prefix_quiet:
    case Nil{} Zero{} unit: {==}
    case Nil{} Succ{prior} unit: L.ex_false({Succ{prior} == 0n : Nat}, quiet_query(tail, prior, V.ReceiptPrepared{receipt, bytes}, suffix_quiet, found))
    case Con{+head, rest} Zero{} L.Both{one, later}:
      L.ex_false({0n == Succ{B.count(V.PreparationEvent, rest)} : Nat}, quiet_not_prepared(head, receipt, bytes, one, F.some_injective(V.PreparationEvent, head, V.ReceiptPrepared{receipt, bytes}, found)))
    case Con{head, +rest} Succ{+prior} L.Both{one, later}:
      Equal.cong(Nat, Nat, n => Succ{n}, prior, B.count(V.PreparationEvent, rest), only(rest, tail, handle, prepared, receipt, bytes, prior, later, suffix_quiet, found))

def wrapped_position(+mode: V.Mode, +raw: P.Request, +context: D.Context, +handle: String, +prepared: List<&2, U32>, last: V.PreparationRun, +receipt: W.Receipt, +bytes: List<&2, U32>, index: Nat,
  quiet: Cause.AllQuiet(V.events(last)), found: {B.query(V.PreparationEvent, V.events(wrapped(mode, raw, context, handle, prepared, last)), index) == Some{V.ReceiptPrepared{receipt, bytes}} : Maybe<&2, V.PreparationEvent>}) -> {index == 4n : Nat}:
  match last:
    case V.PreparationRun{+events, result, snapshot, waiting, closed}: only(prefix(mode, raw, context, handle), events, handle, prepared, receipt, bytes, index, prefix_quiet(mode, raw, context, handle), quiet, found)

def points(+mode: V.Mode, +raw: P.Request, +context: D.Context, +handle: String, bytes: List<&2, U32>, last: V.PreparationRun) ->
  L.E<{B.query(V.PreparationEvent, V.events(wrapped(mode, raw, context, handle, bytes, last)), 2n) == Some{V.Accepted{W.Extension{V.operation(mode), raw}, context}} : Maybe<&2, V.PreparationEvent>},
    {B.query(V.PreparationEvent, V.events(wrapped(mode, raw, context, handle, bytes, last)), 3n) == Some{V.HandleChosen{handle}} : Maybe<&2, V.PreparationEvent>}>:
  match last:
    case V.PreparationRun{events, result, snapshot, waiting, closed}: L.Both{{==}, {==}}
