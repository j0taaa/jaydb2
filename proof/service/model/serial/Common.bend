# Shared concrete phase-result bookkeeping. These records are computed by the
# dispatch functions; no arbitrary completed outcome is an operational premise.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/PreparedLaws.bend as H
import ../../../../contract/Protocol.bend as P
import ../../../../contract/Resources.bend as X
import ../../../../contract/Semantics.bend as S
import ../../../ProtocolService.bend as Q
import ../../../SourceService.bend as Source
import ../../../RoutesService.bend as Route
import ../../specification/ServiceLaws.bend as E
import ../../phases/PreparePhases.bend as V
import ../../phases/InvalidationPhases.bend as N
import ../EventObserver.bend as O

type CallRun is Data:
  CallRun{events: List<&2, O.AuditEvent>, snapshot: E.Snapshot,
    outcome: Maybe<&2, E.Outcome>, waiting: Bool, closed: Bool}

def events(run: CallRun) -> List<&2, O.AuditEvent>:
  CallRun{events, snapshot, outcome, waiting, closed} = run
  events

def snapshot(run: CallRun) -> E.Snapshot:
  CallRun{events, snapshot, outcome, waiting, closed} = run
  snapshot

def waiting(run: CallRun) -> Bool:
  CallRun{events, snapshot, outcome, waiting, closed} = run
  waiting

def closed(run: CallRun) -> Bool:
  CallRun{events, snapshot, outcome, waiting, closed} = run
  closed

def outcome_present(result: Maybe<&2, E.Outcome>) -> Bool:
  match result:
    case None{}: False{}
    case Some{outcome}: True{}

def continues(run: CallRun) -> Bool:
  CallRun{events, snapshot, outcome, waiting, closed} = run
  outcome_present(outcome) && Bool.not(waiting) && Bool.not(closed)

def append(items: List<&2, O.AuditEvent>, suffix: List<&2, O.AuditEvent>) -> List<&2, O.AuditEvent>:
  match items:
    case Nil{}: suffix
    case Con{head, rest}: Con{head, append(rest, suffix)}

def prefix(items: List<&2, O.AuditEvent>, run: CallRun) -> CallRun:
  CallRun{events, snapshot, outcome, waiting, closed} = run
  CallRun{append(items, events), snapshot, outcome, waiting, closed}

def core(+prepared: Bool, +code: String, frames: List<&2, Q.Frame>) -> List<&2, O.AuditEvent>:
  match frames:
    case Nil{}: Nil{}
    case Con{frame, rest}: Con{O.Core{prepared, code, frame}, core(prepared, code, rest)}

def bound_core(+prepared: Bool, +origin: Source.JudgmentSyntactic, frames: List<&2, Q.Frame>) -> List<&2, O.AuditEvent>:
  match frames:
    case Nil{}: Nil{}
    case Con{frame, rest}: Con{O.BoundCore{prepared, origin, frame}, bound_core(prepared, origin, rest)}


def prepare_events(events: List<&2, V.PreparationEvent>) -> List<&2, O.AuditEvent>:
  match events:
    case Nil{}: Nil{}
    case Con{event, rest}: Con{O.Preparation{event}, prepare_events(rest)}

def invalidate_events(events: List<&2, N.InvalidationEvent>) -> List<&2, O.AuditEvent>:
  match events:
    case Nil{}: Nil{}
    case Con{event, rest}: Con{O.Invalidation{event}, invalidate_events(rest)}

def control_outcome(result: Maybe<&2, H.ControlResult>) -> Maybe<&2, E.Outcome>:
  match result:
    case None{}: None{}
    case Some{H.ControlResult{state, entries, H.Metadata{receipt}}}: Some{E.Receipt{receipt}}
    case Some{H.ControlResult{state, entries, H.Error{status}}}: Some{E.Transaction{S.response_error(status)}}

def preparation(run: V.PreparationRun) -> CallRun:
  V.PreparationRun{events, result, snapshot, waiting, closed} = run
  CallRun{prepare_events(events), snapshot, control_outcome(result), waiting, closed}

def invalidation(run: N.InvalidationRun) -> CallRun:
  N.InvalidationRun{events, result, snapshot, waiting, closed} = run
  CallRun{invalidate_events(events), snapshot, control_outcome(result), waiting, closed}

def route_delivery(send: V.SendReturn) -> Route.Delivery:
  match send:
    case V.SendPending{}: Route.PendingDelivery{}
    case V.SendComplete{}: Route.Complete{False{}}
    case V.SendInterrupted{prefix}: Route.Broken{prefix}

def delivery(+mode: Bool, +code: String, +after: E.Snapshot, outcome: E.Outcome, +bytes: List<&2, U32>, +closes: Bool, send: V.SendReturn) -> CallRun:
  match send:
    case V.SendPending{}: CallRun{Nil{}, after, Some{outcome}, True{}, False{}}
    case V.SendComplete{}:
      CallRun{core(mode, code, Route.render_delivery(E.database(after), bytes, closes, Route.Complete{False{}})), after, Some{outcome}, False{}, closes}
    case V.SendInterrupted{prefix}:
      CallRun{core(mode, code, Route.render_delivery(E.database(after), bytes, closes, Route.Broken{prefix})), after, Some{outcome}, False{}, True{}}

def stopped(before: E.Snapshot) -> CallRun:
  CallRun{Nil{}, before, None{}, False{}, False{}}

def pending(before: E.Snapshot) -> CallRun:
  CallRun{Nil{}, before, None{}, True{}, False{}}

def shutdown(+before: E.Snapshot) -> CallRun:
  CallRun{[O.Core{False{}, "", Q.Closed{}}], before, None{}, False{}, True{}}

def error_framed(+mode: Bool, +code: String, +before: E.Snapshot, +status: S.Status, +closes: Bool,
  send: V.SendReturn, frame: Maybe<&2, List<&2, U32>>) -> CallRun:
  match frame:
    case None{}: stopped(before)
    case Some{+bytes}:
      prefix(core(mode, code, [Q.Prepared{S.response_error(status), bytes}, Q.Completed{S.response_error(status), E.database(before), closes}]),
        delivery(mode, code, before, E.Transaction{S.response_error(status)}, bytes, closes, send))

def error(+mode: Bool, code: String, before: E.Snapshot, +status: S.Status, closes: Bool, send: V.SendReturn) -> CallRun:
  error_framed(mode, code, before, status, closes, send, P.frame(S.response_value(S.response_error(status))))

def failed(+mode: Bool, +code: String, +before: E.Snapshot, stage: X.Stage, identifier: String, fatal: Bool, send: V.SendReturn) -> CallRun:
  match fatal:
    case True{}:
      CallRun{core(mode, code, [Q.Failed{stage, identifier, True{}}, Q.Closed{}]), before, None{}, False{}, True{}}
    case False{}:
      prefix(core(mode, code, [Q.Failed{stage, identifier, False{}}]), error(mode, code, before, S.Failure{}, False{}, send))

law waiting_results_cannot_select_the_next_call:
  for events: List<&2, O.AuditEvent>
  for snapshot: E.Snapshot
  for outcome: Maybe<&2, E.Outcome>
  for closed: Bool
  {continues(CallRun{events, snapshot, outcome, True{}, closed}) == False{} : Bool}
def waiting_results_cannot_select_the_next_call(events, snapshot, outcome, closed):
  match outcome:
    case None{}: {==}
    case Some{outcome}: {==}

law absent_conclusion_cannot_fabricate_a_completed_call:
  for -events: List<&2, O.AuditEvent>
  for -snapshot: E.Snapshot
  for -waiting: Bool
  for -closed: Bool
  {continues(CallRun{events, snapshot, None{}, waiting, closed}) == False{} : Bool}
def absent_conclusion_cannot_fabricate_a_completed_call(events, snapshot, waiting, closed):
  {==}
