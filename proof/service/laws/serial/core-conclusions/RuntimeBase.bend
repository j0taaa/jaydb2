# Exact low-level response/conclusion renderers. A transaction conclusion can
# have any response status, including Success/Refusal; no error-name inference.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Resources.bend as X
import ../../../../../contract/Semantics.bend as S
import ../../../../ProtocolService.bend as Q
import ../../../../RoutesService.bend as Route
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../model/EventObserver.bend as O
import ../../../model/serial/Common.bend as C
import ./Meaning.bend as M
import ./Algebra.bend as A

def ordinary_frame(frame: Q.Frame) -> {M.frame_end(False{}, frame) == None{} : Maybe<&2, M.Endpoint>}:
  match frame:
    case Q.Configured{}: {==}
    case Q.InitialAccepts{}: {==}
    case Q.Initialized{state}: {==}
    case Q.InitialRefused{status}: {==}
    case Q.Encoded{value, bytes}: {==}
    case Q.Decoded{bytes, value}: {==}
    case Q.Stored{state, bytes, abstraction}: {==}
    case Q.Checked{position, count}: {==}
    case Q.Constructed{position, count}: {==}
    case Q.Read{before, count, declared}: {==}
    case Q.Received{request}: {==}
    case Q.Authenticated{request, context}: {==}
    case Q.Accepts{request, context}: {==}
    case Q.Rejected{request, context}: {==}
    case Q.Started{request, context}: {==}
    case Q.Evaluated{request, context, execution_trace}: {==}
    case Q.Operated{schema, state, operation, result}: {==}
    case Q.Prepared{response, bytes}: {==}
    case Q.Published{state}: {==}
    case Q.Visible{state}: {==}
    case Q.Failed{stage, identifier, fatal}: {==}
    case Q.Completed{response, state, closes}: {==}
    case Q.Delivered{bytes}: {==}
    case Q.Interrupted{prefix}: {==}
    case Q.Closed{}: {==}
    case Q.Next{previous, initial}: {==}
    case Q.Inspection{description}: {==}
    case Q.Effect{description}: {==}


def ordinary_core(+code: String, frames: List<&2, Q.Frame>) -> {M.quiet(C.core(False{}, code, frames)) == True{} : Bool}:
  match frames:
    case Nil{}: {==}
    case Con{+head, +rest}:
      A.quiet_cons(O.Core{False{}, code, head}, C.core(False{}, code, rest),
        (%Equal.sym(Maybe<&2, M.Endpoint>, M.frame_end(False{}, head), None{}, ordinary_frame(head)) : {M.absent(_) == True{} : Bool} {==}), ordinary_core(code, rest))

def quiet_later_delivery(+mode: Bool, +code: String, +state: D.State, closes: Bool, next: Bool) ->
  {M.quiet(C.core(mode, code, Route.later_delivery(closes, state, next))) == True{} : Bool}:
  match closes next:
    case True{} _: {==}
    case False{} True{}: {==}
    case False{} False{}: {==}

def quiet_render_delivery(+mode: Bool, +code: String, +state: D.State, +bytes: List<&2, U32>, +closes: Bool, delivery: Route.Delivery) ->
  {M.quiet(C.core(mode, code, Route.render_delivery(state, bytes, closes, delivery))) == True{} : Bool}:
  match delivery:
    case Route.PendingDelivery{}: {==}
    case Route.Broken{prefix}: {==}
    case Route.Complete{+next}:
      A.quiet_cons(O.Core{mode, code, Q.Delivered{bytes}}, C.core(mode, code, Route.later_delivery(closes, state, next)), {==}, quiet_later_delivery(mode, code, state, closes, next))

def quiet_delivery(+mode: Bool, +code: String, +after: E.Snapshot, +outcome: E.Outcome, +bytes: List<&2, U32>, +closes: Bool, send: V.SendReturn) ->
  {M.quiet(C.events(C.delivery(mode, code, after, outcome, bytes, closes, send))) == True{} : Bool}:
  match send:
    case V.SendPending{}: {==}
    case V.SendComplete{}: quiet_render_delivery(mode, code, E.database(after), bytes, closes, Route.Complete{False{}})
    case V.SendInterrupted{prefix}: quiet_render_delivery(mode, code, E.database(after), bytes, closes, Route.Broken{prefix})

def stopped(+before: E.Snapshot) -> M.Shape<C.events(C.stopped(before))>: M.Quiet{{==}}
def pending(+before: E.Snapshot) -> M.Shape<C.events(C.pending(before))>: M.Quiet{{==}}
def shutdown(+before: E.Snapshot) -> M.Shape<C.events(C.shutdown(before))>: M.Quiet{{==}}

def ordinary_error_framed(+code: String, +before: E.Snapshot, +status: S.Status, +closes: Bool, +send: V.SendReturn,
  frame: Maybe<&2, List<&2, U32>>) -> {M.quiet(C.events(C.error_framed(False{}, code, before, status, closes, send, frame))) == True{} : Bool}:
  match frame:
    case None{}: {==}
    case Some{+bytes}:
      %Equal.sym(List<&2, O.AuditEvent>, C.events(C.prefix(C.core(False{}, code, [Q.Prepared{S.response_error(status), bytes}, Q.Completed{S.response_error(status), E.database(before), closes}]),
        C.delivery(False{}, code, before, E.Transaction{S.response_error(status)}, bytes, closes, send))),
        C.append(C.core(False{}, code, [Q.Prepared{S.response_error(status), bytes}, Q.Completed{S.response_error(status), E.database(before), closes}]), C.events(C.delivery(False{}, code, before, E.Transaction{S.response_error(status)}, bytes, closes, send))),
        A.prefix_events(C.core(False{}, code, [Q.Prepared{S.response_error(status), bytes}, Q.Completed{S.response_error(status), E.database(before), closes}]), C.delivery(False{}, code, before, E.Transaction{S.response_error(status)}, bytes, closes, send))) : {M.quiet(_) == True{} : Bool}
      A.quiet_append(C.core(False{}, code, [Q.Prepared{S.response_error(status), bytes}, Q.Completed{S.response_error(status), E.database(before), closes}]), C.events(C.delivery(False{}, code, before, E.Transaction{S.response_error(status)}, bytes, closes, send)),
        ordinary_core(code, [Q.Prepared{S.response_error(status), bytes}, Q.Completed{S.response_error(status), E.database(before), closes}]),
        quiet_delivery(False{}, code, before, E.Transaction{S.response_error(status)}, bytes, closes, send))

def prepared_error_framed(+code: String, +before: E.Snapshot, +status: S.Status, +send: V.SendReturn,
  frame: Maybe<&2, List<&2, U32>>) -> M.Shape<C.events(C.error_framed(True{}, code, before, status, False{}, send, frame))>:
  match frame:
    case None{}: stopped(before)
    case Some{+bytes}:
      %Equal.sym(List<&2, O.AuditEvent>, C.events(C.error_framed(True{}, code, before, status, False{}, send, Some{bytes})),
        C.append(C.core(True{}, code, [Q.Prepared{S.response_error(status), bytes}, Q.Completed{S.response_error(status), E.database(before), False{}}]), C.events(C.delivery(True{}, code, before, E.Transaction{S.response_error(status)}, bytes, False{}, send))),
        A.prefix_events(C.core(True{}, code, [Q.Prepared{S.response_error(status), bytes}, Q.Completed{S.response_error(status), E.database(before), False{}}]), C.delivery(True{}, code, before, E.Transaction{S.response_error(status)}, bytes, False{}, send))) : M.Shape<_>
      M.TransactionShape{[O.Core{True{}, code, Q.Prepared{S.response_error(status), bytes}}], C.events(C.delivery(True{}, code, before, E.Transaction{S.response_error(status)}, bytes, False{}, send)),
        O.Core{True{}, code, Q.Completed{S.response_error(status), E.database(before), False{}}}, S.response_error(status), E.database(before), bytes, 0n, O.Core{True{}, code, Q.Prepared{S.response_error(status), bytes}},
        {==}, {==}, {==}, quiet_delivery(True{}, code, before, E.Transaction{S.response_error(status)}, bytes, False{}, send), {==}, {==}}

def SafeClosing(mode: Bool, -closes: Bool) -> Type:
  match mode:
    case False{}: Unit
    case True{}: {closes == False{} : Bool}

def error_framed(mode: Bool, +code: String, +before: E.Snapshot, +status: S.Status, +closes: Bool, +send: V.SendReturn,
  +frame: Maybe<&2, List<&2, U32>>, safe: SafeClosing(mode, closes)) -> M.Shape<C.events(C.error_framed(mode, code, before, status, closes, send, frame))>:
  match mode:
    case False{}: M.Quiet{ordinary_error_framed(code, before, status, closes, send, frame)}
    case True{}:
      %Equal.sym(Bool, closes, False{}, safe) : M.Shape<C.events(C.error_framed(True{}, code, before, status, _, send, frame))>
      prepared_error_framed(code, before, status, send, frame)

def error(+mode: Bool, +code: String, +before: E.Snapshot, +status: S.Status, +closes: Bool, +send: V.SendReturn,
  safe: SafeClosing(mode, closes)) -> M.Shape<C.events(C.error(mode, code, before, status, closes, send))>:
  error_framed(mode, code, before, status, closes, send, P.frame(S.response_value(S.response_error(status))), safe)

def false_is_safe(mode: Bool) -> SafeClosing(mode, False{}):
  match mode:
    case False{}: Unit{}
    case True{}: {==}

def failed(+mode: Bool, +code: String, +before: E.Snapshot, +stage: X.Stage, +identifier: String, fatal: Bool, +send: V.SendReturn) ->
  M.Shape<C.events(C.failed(mode, code, before, stage, identifier, fatal, send))>:
  match fatal:
    case True{}: M.Quiet{{==}}
    case False{}:
      A.prefix_run(C.core(mode, code, [Q.Failed{stage, identifier, False{}}]), C.error(mode, code, before, S.Failure{}, False{}, send), {==}, error(mode, code, before, S.Failure{}, False{}, send, false_is_safe(mode)))
