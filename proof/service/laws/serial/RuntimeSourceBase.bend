# Shared actual syntax of common runtime renderers. Every return and event
# is retained; the property excludes all control-phase constructors.
import Base
import ../../../../contract/Logic.bend as L
import ../../../../contract/Protocol.bend as P
import ../../../../contract/Resources.bend as X
import ../../../../contract/Semantics.bend as S
import ../../../ProtocolService.bend as Q
import ../../../RoutesService.bend as Route
import ../../../SourceService.bend as Source
import ../../specification/ServiceLaws.bend as E
import ../../phases/PreparePhases.bend as V
import ../../phases/InvalidationPhases.bend as N
import ../../model/EventObserver.bend as O
import ../../model/serial/Common.bend as C


import ./RuntimeSyntax.bend as Syntax


def All(events: List<&2, O.AuditEvent>) -> Type:
  Syntax.All(events)


def Call(run: C.CallRun) -> Type:
  All(C.events(run))


def appended(+first: List<&2, O.AuditEvent>, -last: List<&2, O.AuditEvent>, a: All(first), b: All(last)) -> All(C.append(first, last)):
  match first a:
    case Nil{} unit: b
    case Con{head, +rest} L.Both{first, later}: L.Both{first, appended(rest, last, later, b)}


def prefixed(+prefix: List<&2, O.AuditEvent>, run: C.CallRun, first: All(prefix), later: Call(run)) -> Call(C.prefix(prefix, run)):
  match run:
    case C.CallRun{events, snapshot, outcome, waiting, closed}: appended(prefix, events, first, later)


def core(+mode: Bool, +code: String, frames: List<&2, Q.Frame>) -> All(C.core(mode, code, frames)):
  match frames:
    case Nil{}: Unit{}
    case Con{frame, rest}: L.Both{Unit{}, core(mode, code, rest)}


def bound_core(+mode: Bool, +origin: Source.JudgmentSyntactic, frames: List<&2, Q.Frame>) -> All(C.bound_core(mode, origin, frames)):
  match frames:
    case Nil{}: Unit{}
    case Con{frame, rest}: L.Both{Unit{}, bound_core(mode, origin, rest)}


def delivery(+mode: Bool, +code: String, +after: E.Snapshot, outcome: E.Outcome,
  +bytes: List<&2, U32>, +closes: Bool, send: V.SendReturn) -> Call(C.delivery(mode, code, after, outcome, bytes, closes, send)):
  match send:
    case V.SendPending{}: Unit{}
    case V.SendComplete{}: core(mode, code, Route.render_delivery(E.database(after), bytes, closes, Route.Complete{False{}}))
    case V.SendInterrupted{prefix}: core(mode, code, Route.render_delivery(E.database(after), bytes, closes, Route.Broken{prefix}))


def error_framed(+mode: Bool, +code: String, +before: E.Snapshot, +status: S.Status, +closes: Bool,
  +send: V.SendReturn, frame: Maybe<&2, List<&2, U32>>) -> Call(C.error_framed(mode, code, before, status, closes, send, frame)):
  match frame:
    case None{}: Unit{}
    case Some{+bytes}:
      prefixed(C.core(mode, code, [Q.Prepared{S.response_error(status), bytes}, Q.Completed{S.response_error(status), E.database(before), closes}]),
        C.delivery(mode, code, before, E.Transaction{S.response_error(status)}, bytes, closes, send),
        core(mode, code, [Q.Prepared{S.response_error(status), bytes}, Q.Completed{S.response_error(status), E.database(before), closes}]),
        delivery(mode, code, before, E.Transaction{S.response_error(status)}, bytes, closes, send))


def error(+mode: Bool, +code: String, +before: E.Snapshot, +status: S.Status, +closes: Bool, +send: V.SendReturn) ->
  Call(C.error(mode, code, before, status, closes, send)):
  error_framed(mode, code, before, status, closes, send, P.frame(S.response_value(S.response_error(status))))


def failed(+mode: Bool, +code: String, +before: E.Snapshot, +stage: X.Stage, +identifier: String, fatal: Bool, +send: V.SendReturn) ->
  Call(C.failed(mode, code, before, stage, identifier, fatal, send)):
  match fatal:
    case True{}: core(mode, code, [Q.Failed{stage, identifier, True{}}, Q.Closed{}])
    case False{}:
      prefixed(C.core(mode, code, [Q.Failed{stage, identifier, False{}}]), C.error(mode, code, before, S.Failure{}, False{}, send),
        core(mode, code, [Q.Failed{stage, identifier, False{}}]), error(mode, code, before, S.Failure{}, False{}, send))
