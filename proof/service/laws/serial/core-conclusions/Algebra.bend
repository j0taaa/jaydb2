# List occurrence algebra. These premises are internal component facts; the
# final source theorem derives them from actual runtime constructors.
import Base
import ../../../../Foundations.bend as F
import ../../../model/EventObserver.bend as O
import ../../../model/FrameBounds.bend as B
import ../../../model/serial/Common.bend as C
import ../../../model/serial/AuditQueries.bend as Query
import ./Meaning.bend as M

def append_assoc(+first: List<&2, O.AuditEvent>, +second: List<&2, O.AuditEvent>, +third: List<&2, O.AuditEvent>) ->
  {C.append(C.append(first, second), third) == C.append(first, C.append(second, third)) : List<&2, O.AuditEvent>}:
  match first:
    case Nil{}: {==}
    case Con{+head, rest}:
      Equal.cong(List<&2, O.AuditEvent>, List<&2, O.AuditEvent>, tail => Con{head, tail}, C.append(C.append(rest, second), third), C.append(rest, C.append(second, third)), append_assoc(rest, second, third))

def quiet_cons(+head: O.AuditEvent, +tail: List<&2, O.AuditEvent>,
  first: {M.absent(M.endpoint(head)) == True{} : Bool}, later: {M.quiet(tail) == True{} : Bool}) ->
  {M.quiet(Con{head, tail}) == True{} : Bool}:
  %Equal.sym(Bool, M.absent(M.endpoint(head)), True{}, first) : {(_ && M.quiet(tail)) == True{} : Bool}
  %Equal.sym(Bool, M.quiet(tail), True{}, later) : {(True{} && _) == True{} : Bool}
  {==}

def quiet_append(+first: List<&2, O.AuditEvent>, +second: List<&2, O.AuditEvent>,
  +front: {M.quiet(first) == True{} : Bool}, rear: {M.quiet(second) == True{} : Bool}) ->
  {M.quiet(C.append(first, second)) == True{} : Bool}:
  match first:
    case Nil{}: rear
    case Con{+head, +rest}:
      quiet_cons(head, C.append(rest, second), F.and_boolean_left(M.absent(M.endpoint(head)), M.quiet(rest), front),
        quiet_append(rest, second, F.and_boolean_right(M.absent(M.endpoint(head)), M.quiet(rest), front), rear))

def prepend_layout(+front: List<&2, O.AuditEvent>, +events: List<&2, O.AuditEvent>,
  +prefix: List<&2, O.AuditEvent>, +event: O.AuditEvent, +suffix: List<&2, O.AuditEvent>,
  layout: {events == C.append(prefix, Con{event, suffix}) : List<&2, O.AuditEvent>}) ->
  {C.append(front, events) == C.append(C.append(front, prefix), Con{event, suffix}) : List<&2, O.AuditEvent>}:
  Equal.trans(List<&2, O.AuditEvent>, C.append(front, events), C.append(front, C.append(prefix, Con{event, suffix})), C.append(C.append(front, prefix), Con{event, suffix}),
    Equal.cong(List<&2, O.AuditEvent>, List<&2, O.AuditEvent>, rest => C.append(front, rest), events, C.append(prefix, Con{event, suffix}), layout),
    Equal.sym(List<&2, O.AuditEvent>, C.append(C.append(front, prefix), Con{event, suffix}), C.append(front, C.append(prefix, Con{event, suffix})), append_assoc(front, prefix, Con{event, suffix})))

def prepend(+front: List<&2, O.AuditEvent>, +events: List<&2, O.AuditEvent>,
  +quiet: {M.quiet(front) == True{} : Bool}, shape: M.Shape<events>) -> M.Shape<C.append(front, events)>:
  match shape:
    case M.Quiet{none}: M.Quiet{quiet_append(front, events, quiet, none)}
    case M.TransactionShape{+prefix, +suffix, +event, response, state, bytes, +prepared_at, +prepared_event, layout, concluded, left, right, query, payload}:
      M.TransactionShape{C.append(front, prefix), suffix, event, response, state, bytes, Nat.add(B.count(O.AuditEvent, front), prepared_at), prepared_event,
        prepend_layout(front, events, prefix, event, suffix, layout), concluded, quiet_append(front, prefix, quiet, left), right,
        Query.suffix_query(front, prefix, prepared_at, prepared_event, query), payload}
    case M.MetadataShape{+prefix, +suffix, +event, receipt, result, snapshot, closes, layout, concluded, left, right}:
      M.MetadataShape{C.append(front, prefix), suffix, event, receipt, result, snapshot, closes,
        prepend_layout(front, events, prefix, event, suffix, layout), concluded, quiet_append(front, prefix, quiet, left), right}

def prefix_events(+events: List<&2, O.AuditEvent>, run: C.CallRun) ->
  {C.events(C.prefix(events, run)) == C.append(events, C.events(run)) : List<&2, O.AuditEvent>}:
  match run:
    case C.CallRun{tail, snapshot, outcome, waiting, closed}: {==}

def prefix_run(+front: List<&2, O.AuditEvent>, +run: C.CallRun,
  quiet: {M.quiet(front) == True{} : Bool}, shape: M.Shape<C.events(run)>) -> M.Shape<C.events(C.prefix(front, run))>:
  %Equal.sym(List<&2, O.AuditEvent>, C.events(C.prefix(front, run)), C.append(front, C.events(run)), prefix_events(front, run)) : M.Shape<_>
  prepend(front, C.events(run), quiet, shape)
