# Queried receipt occurrence -> exact real earlier acceptance/choice queries.
# The public boundary supplies only original inputs and an actual query.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Semantics.bend as S
import ../../../../Foundations.bend as F
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../model/FrameBounds.bend as B
import ./PreparationCauses.bend as Cause
import ./PreparationPrefix.bend as Prefix

def receipt_of(event: V.PreparationEvent) -> Maybe<&2, W.Receipt>:
  match event:
    case V.ReceiptPrepared{receipt, bytes}: Some{receipt}
    case _: None{}

type Site<-mode: V.Mode, -raw: P.Request, -events: List<&2, V.PreparationEvent>, -index: Nat, -receipt: W.Receipt> is Data:
  Site{context: D.Context, handle: String,
    payload: {receipt == W.PreparedReceipt{handle} : W.Receipt},
    position: {index == 4n : Nat},
    accepted: {B.query(V.PreparationEvent, events, 2n) == Some{V.Accepted{W.Extension{V.operation(mode), raw}, context}} : Maybe<&2, V.PreparationEvent>},
    chosen: {B.query(V.PreparationEvent, events, 3n) == Some{V.HandleChosen{handle}} : Maybe<&2, V.PreparationEvent>}}

def make(-mode: V.Mode, -raw: P.Request, -events: List<&2, V.PreparationEvent>, -index: Nat, -receipt: W.Receipt, context: D.Context, handle: String,
  payload: {receipt == W.PreparedReceipt{handle} : W.Receipt}, position: {index == 4n : Nat},
  points: L.E<{B.query(V.PreparationEvent, events, 2n) == Some{V.Accepted{W.Extension{V.operation(mode), raw}, context}} : Maybe<&2, V.PreparationEvent>},
    {B.query(V.PreparationEvent, events, 3n) == Some{V.HandleChosen{handle}} : Maybe<&2, V.PreparationEvent>}>) -> Site<mode, raw, events, index, receipt>:
  match points:
    case L.Both{accepted, chosen}: Site{context, handle, payload, position, accepted, chosen}

def wrapped(+mode: V.Mode, +raw: P.Request, +context: D.Context, +handle: String, +prepared: List<&2, U32>, +tail: V.PreparationRun, +receipt: W.Receipt, +bytes: List<&2, U32>, +index: Nat,
  payload: {receipt == W.PreparedReceipt{handle} : W.Receipt}, quiet: Cause.AllQuiet(V.events(tail)),
  found: {B.query(V.PreparationEvent, V.events(Prefix.wrapped(mode, raw, context, handle, prepared, tail)), index) == Some{V.ReceiptPrepared{receipt, bytes}} : Maybe<&2, V.PreparationEvent>}) ->
  Site<mode, raw, V.events(Prefix.wrapped(mode, raw, context, handle, prepared, tail)), index, receipt>:
  make(mode, raw, V.events(Prefix.wrapped(mode, raw, context, handle, prepared, tail)), index, receipt, context, handle, payload,
    Prefix.wrapped_position(mode, raw, context, handle, prepared, tail, receipt, bytes, index, quiet, found), Prefix.points(mode, raw, context, handle, prepared, tail))

def source(~c: S.Configuration, +mode: V.Mode, +raw: P.Request, +before: E.Snapshot, +returns: V.Returns, +context: D.Context, +handle: String, +seal: V.SealReturn, +prepared: List<&2, U32>, +send: V.SendReturn,
  +receipt: W.Receipt, +bytes: List<&2, U32>, +index: Nat,
  payload: {receipt == W.PreparedReceipt{handle} : W.Receipt},
  +exact: {V.run(c, mode, raw, before, returns) == Prefix.wrapped(mode, raw, context, handle, prepared, V.seal_result(c, seal, mode, raw, before, handle, prepared, send)) : V.PreparationRun},
  found: {B.query(V.PreparationEvent, V.events(V.run(c, mode, raw, before, returns)), index) == Some{V.ReceiptPrepared{receipt, bytes}} : Maybe<&2, V.PreparationEvent>}) ->
  Site<mode, raw, V.events(V.run(c, mode, raw, before, returns)), index, receipt>:
  %Equal.sym(V.PreparationRun, V.run(c, mode, raw, before, returns), Prefix.wrapped(mode, raw, context, handle, prepared, V.seal_result(c, seal, mode, raw, before, handle, prepared, send)), exact) : Site<mode, raw, V.events(_), index, receipt>
  wrapped(mode, raw, context, handle, prepared, V.seal_result(c, seal, mode, raw, before, handle, prepared, send), receipt, bytes, index, payload,
    Cause.quiet_sealed(c, mode, raw, before, handle, seal, prepared, send),
    Equal.trans(Maybe<&2, V.PreparationEvent>, B.query(V.PreparationEvent, V.events(Prefix.wrapped(mode, raw, context, handle, prepared, V.seal_result(c, seal, mode, raw, before, handle, prepared, send))), index),
      B.query(V.PreparationEvent, V.events(V.run(c, mode, raw, before, returns)), index), Some{V.ReceiptPrepared{receipt, bytes}},
      Equal.sym(Maybe<&2, V.PreparationEvent>, B.query(V.PreparationEvent, V.events(V.run(c, mode, raw, before, returns)), index), B.query(V.PreparationEvent, V.events(Prefix.wrapped(mode, raw, context, handle, prepared, V.seal_result(c, seal, mode, raw, before, handle, prepared, send))), index),
        Equal.cong(V.PreparationRun, Maybe<&2, V.PreparationEvent>, r => B.query(V.PreparationEvent, V.events(r), index), V.run(c, mode, raw, before, returns), Prefix.wrapped(mode, raw, context, handle, prepared, V.seal_result(c, seal, mode, raw, before, handle, prepared, send)), exact)), found))

def from_cause(~c: S.Configuration, +mode: V.Mode, +raw: P.Request, +before: E.Snapshot, +returns: V.Returns, +receipt: W.Receipt, +bytes: List<&2, U32>, +index: Nat,
  found: {B.query(V.PreparationEvent, V.events(V.run(c, mode, raw, before, returns)), index) == Some{V.ReceiptPrepared{receipt, bytes}} : Maybe<&2, V.PreparationEvent>},
  cause: Cause.Cause<c, mode, raw, before, returns, V.ReceiptPrepared{receipt, bytes}>) -> Site<mode, raw, V.events(V.run(c, mode, raw, before, returns)), index, receipt>:
  match cause:
    case Cause.Cause{+context, +handle, +seal, +prepared, +send, auth, returned, fits, frame, payload}:
      source(c, mode, raw, before, returns, context, handle, seal, prepared, send, receipt, bytes, index,
        F.some_injective(W.Receipt, receipt, W.PreparedReceipt{handle}, Equal.cong(V.PreparationEvent, Maybe<&2, W.Receipt>, receipt_of, V.ReceiptPrepared{receipt, bytes}, V.ReceiptPrepared{W.PreparedReceipt{handle}, prepared}, payload)),
        Equal.trans(V.PreparationRun, V.run(c, mode, raw, before, returns), V.run(c, mode, raw, before, V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, seal, send}), Prefix.wrapped(mode, raw, context, handle, prepared, V.seal_result(c, seal, mode, raw, before, handle, prepared, send)),
          Equal.cong(V.Returns, V.PreparationRun, r => V.run(c, mode, raw, before, r), returns, V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, seal, send}, returned),
          Prefix.actual(c, mode, raw, before, context, handle, seal, prepared, send, auth, fits, frame)), found)

law every_actual_queried_prepared_receipt_has_its_exact_earlier_acceptance_and_handle_choice:
  for ~c: S.Configuration
  for +mode: V.Mode
  for +raw: P.Request
  for +before: E.Snapshot
  for +returns: V.Returns
  for +receipt: W.Receipt
  for +bytes: List<&2, U32>
  for +index: Nat
  for +found: {B.query(V.PreparationEvent, V.events(V.run(c, mode, raw, before, returns)), index) == Some{V.ReceiptPrepared{receipt, bytes}} : Maybe<&2, V.PreparationEvent>}
  Site<mode, raw, V.events(V.run(c, mode, raw, before, returns)), index, receipt>
def every_actual_queried_prepared_receipt_has_its_exact_earlier_acceptance_and_handle_choice(c, mode, raw, before, returns, receipt, bytes, index, found):
  from_cause(c, mode, raw, before, returns, receipt, bytes, index, found,
    Cause.any_actual_queried_prepared_receipt_recovers_its_original_inputs_before_any_seal_result(c, mode, raw, before, returns, index, receipt, bytes, found))
