# Exact invalidation receipt position and pre-removal identity, ALL cleanup returns.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Resources.bend as X
import ../../../../../contract/Semantics.bend as S
import ../../../../Foundations.bend as F
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../phases/InvalidationPhases.bend as N
import ../../../phases/InvalidationEvents.bend as Original
import ../../../model/FrameBounds.bend as B
import ./PreparationCauses.bend as Preparation
import ./InvalidationCauses.bend as Cause

def Quiet(event: N.InvalidationEvent) -> Type:
  match event:
    case N.InvalidationBase{phase}: Preparation.Quiet(phase)
    case N.RegistryRemoved{handle, before, after}: Unit

def All(events: List<&2, N.InvalidationEvent>) -> Type:
  match events:
    case Nil{}: Unit
    case Con{head, tail}: L.E<Quiet(head), All(tail)>

def base(events: List<&2, V.PreparationEvent>, quiet: Preparation.AllQuiet(events)) -> All(N.base_events(events)):
  match events quiet:
    case Nil{} unit: Unit{}
    case Con{event, tail} L.Both{head, later}: L.Both{head, base(tail, later)}

def lift(run: V.PreparationRun, quiet: Preparation.AllQuiet(V.events(run))) -> All(N.events(N.lift(run))):
  match run:
    case V.PreparationRun{events, result, snapshot, waiting, closed}: base(events, quiet)

def push(+event: N.InvalidationEvent, run: N.InvalidationRun, head: Quiet(event), later: All(N.events(run))) -> All(N.events(N.push(event, run))):
  match run:
    case N.InvalidationRun{events, result, snapshot, waiting, closed}: L.Both{head, later}

def cleaned(+snapshot: E.Snapshot, +bytes: List<&2, U32>, cleanup: N.CleanupReturn, +send: V.SendReturn) -> All(N.events(N.cleaned(cleanup, snapshot, bytes, send))):
  match cleanup:
    case N.CleanupPending{}: lift(V.pending(snapshot), Unit{})
    case N.CleanupFailed{+identifier, +fatal}: lift(V.failed(X.Prepare{}, identifier, fatal, snapshot, send), Preparation.quiet_failed(X.Prepare{}, identifier, fatal, snapshot, send))
    case N.CleanupComplete{}:
      lift(V.push(V.ReceiptConcluded{W.InvalidatedReceipt{}, N.metadata(snapshot), snapshot, False{}}, V.delivery(send, bytes, N.metadata(snapshot), snapshot)),
        Preparation.quiet_prepend(V.ReceiptConcluded{W.InvalidatedReceipt{}, N.metadata(snapshot), snapshot, False{}}, V.delivery(send, bytes, N.metadata(snapshot), snapshot), Unit{}, Preparation.quiet_delivery(send, bytes, N.metadata(snapshot), snapshot)))

def removed(+before: E.Snapshot, +raw: P.Request, +bytes: List<&2, U32>, +cleanup: N.CleanupReturn, +send: V.SendReturn) -> All(N.events(N.remove_and_cleanup(before, I.code(raw), bytes, cleanup, send))):
  push(N.RegistryRemoved{I.code(raw), before, N.removed(before, I.code(raw))}, N.cleaned(cleanup, N.removed(before, I.code(raw)), bytes, send), Unit{}, cleaned(N.removed(before, I.code(raw)), bytes, cleanup, send))

def append(prefix: List<&2, N.InvalidationEvent>, tail: List<&2, N.InvalidationEvent>) -> List<&2, N.InvalidationEvent>:
  match prefix:
    case Nil{}: tail
    case Con{head, rest}: Con{head, append(rest, tail)}

def quiet_query(+events: List<&2, N.InvalidationEvent>, index: Nat, +receipt: W.Receipt, +bytes: List<&2, U32>, quiet: All(events),
  found: {B.query(N.InvalidationEvent, events, index) == Some{N.InvalidationBase{V.ReceiptPrepared{receipt, bytes}}} : Maybe<&2, N.InvalidationEvent>}) -> Empty:
  match events index quiet:
    case Nil{} _ unit: F.none_negative_some(N.InvalidationEvent, N.InvalidationBase{V.ReceiptPrepared{receipt, bytes}}, found)
    case Con{+head, tail} Zero{} L.Both{one, later}:
      %F.some_injective(N.InvalidationEvent, head, N.InvalidationBase{V.ReceiptPrepared{receipt, bytes}}, found) : Quiet(_) one
    case Con{head, +tail} Succ{prior} L.Both{one, later}: quiet_query(tail, prior, receipt, bytes, later, found)

def only(+prefix: List<&2, N.InvalidationEvent>, +tail: List<&2, N.InvalidationEvent>, +prepared: List<&2, U32>, +receipt: W.Receipt, +bytes: List<&2, U32>, index: Nat,
  early: All(prefix), later: All(tail),
  found: {B.query(N.InvalidationEvent, append(prefix, Con{N.InvalidationBase{V.ReceiptPrepared{W.InvalidatedReceipt{}, prepared}}, tail}), index) == Some{N.InvalidationBase{V.ReceiptPrepared{receipt, bytes}}} : Maybe<&2, N.InvalidationEvent>}) -> {index == B.count(N.InvalidationEvent, prefix) : Nat}:
  match prefix index early:
    case Nil{} Zero{} unit: {==}
    case Nil{} Succ{prior} unit: L.ex_false({Succ{prior} == 0n : Nat}, quiet_query(tail, prior, receipt, bytes, later, found))
    case Con{+head, rest} Zero{} L.Both{one, following}:
      L.ex_false({0n == Succ{B.count(N.InvalidationEvent, rest)} : Nat},
        quiet_query(Con{head, Nil{}}, 0n, receipt, bytes, L.Both{one, Unit{}}, found))
    case Con{head, +rest} Succ{+prior} L.Both{one, following}:
      Equal.cong(Nat, Nat, n => Succ{n}, prior, B.count(N.InvalidationEvent, rest), only(rest, tail, prepared, receipt, bytes, prior, following, later, found))

def wrapped(+raw: P.Request, context: D.Context, +prepared: List<&2, U32>, tail: N.InvalidationRun) -> N.InvalidationRun:
  N.push(N.InvalidationBase{V.WireReceived{W.Extension{W.Invalidate{}, raw}}}, N.push(N.InvalidationBase{V.IdentityEstablished{W.Extension{W.Invalidate{}, raw}, Some{context}}}, N.push(N.InvalidationBase{V.ReceiptPrepared{W.InvalidatedReceipt{}, prepared}}, tail)))

def prefix(+raw: P.Request, context: D.Context) -> List<&2, N.InvalidationEvent>:
  [N.InvalidationBase{V.WireReceived{W.Extension{W.Invalidate{}, raw}}}, N.InvalidationBase{V.IdentityEstablished{W.Extension{W.Invalidate{}, raw}, Some{context}}}]

def position_wrapped(+raw: P.Request, +context: D.Context, +prepared: List<&2, U32>, tail: N.InvalidationRun, +receipt: W.Receipt, +bytes: List<&2, U32>, index: Nat,
  quiet: All(N.events(tail)), found: {B.query(N.InvalidationEvent, N.events(wrapped(raw, context, prepared, tail)), index) == Some{N.InvalidationBase{V.ReceiptPrepared{receipt, bytes}}} : Maybe<&2, N.InvalidationEvent>}) -> {index == 2n : Nat}:
  match tail:
    case N.InvalidationRun{+events, result, snapshot, waiting, closed}: only(prefix(raw, context), events, prepared, receipt, bytes, index, L.Both{Unit{}, L.Both{Unit{}, Unit{}}}, quiet, found)

def from_cause(~c: S.Configuration, +before: E.Snapshot, +raw: P.Request, +cleanup: N.CleanupReturn, +send: V.SendReturn, +receipt: W.Receipt, +bytes: List<&2, U32>, +index: Nat,
  found: {B.query(N.InvalidationEvent, N.events(N.run(c, before, raw, cleanup, send)), index) == Some{N.InvalidationBase{V.ReceiptPrepared{receipt, bytes}}} : Maybe<&2, N.InvalidationEvent>},
  cause: Cause.Cause<c, before, raw, cleanup, send, V.ReceiptPrepared{receipt, bytes}>) -> {index == 2n : Nat}:
  match cause:
    case Cause.Cause{+context, +entry, +prepared, auth, empty, lookup, fits, frame, payload}:
      position_wrapped(raw, context, prepared, N.remove_and_cleanup(before, I.code(raw), prepared, cleanup, send), receipt, bytes, index, removed(before, raw, prepared, cleanup, send),
        %Original.actual_authorized_framed_invalidation_has_its_exact_removal_phases(c, before, raw, entry, context, prepared, cleanup, send, auth, empty, lookup, fits, frame) :
          {B.query(N.InvalidationEvent, N.events(_), index) == Some{N.InvalidationBase{V.ReceiptPrepared{receipt, bytes}}} : Maybe<&2, N.InvalidationEvent>}
        found)

law every_actual_queried_invalidation_receipt_frame_occurs_before_removal_at_phase_two:
  for ~c: S.Configuration
  for +before: E.Snapshot
  for +raw: P.Request
  for +cleanup: N.CleanupReturn
  for +send: V.SendReturn
  for +receipt: W.Receipt
  for +bytes: List<&2, U32>
  for +index: Nat
  for +found: {B.query(N.InvalidationEvent, N.events(N.run(c, before, raw, cleanup, send)), index) == Some{N.InvalidationBase{V.ReceiptPrepared{receipt, bytes}}} : Maybe<&2, N.InvalidationEvent>}
  {index == 2n : Nat}
def every_actual_queried_invalidation_receipt_frame_occurs_before_removal_at_phase_two(c, before, raw, cleanup, send, receipt, bytes, index, found):
  from_cause(c, before, raw, cleanup, send, receipt, bytes, index, found, Cause.any_actual_queried_invalidation_receipt_frame_recovers_its_original_guards_without_cleanup_completion(c, before, raw, cleanup, send, index, receipt, bytes, found))
