# Every shared error/delivery helper preserves its exact complete snapshot and
# contributes only its actual ordinary frames, including interruption/closure.
import Base
import ../../../../contract/Protocol.bend as P
import ../../../../contract/Resources.bend as X
import ../../../../contract/Semantics.bend as S
import ../../../RoutesService.bend as Route
import ../../../ProtocolService.bend as Q
import ../../specification/ServiceLaws.bend as E
import ../../phases/PreparePhases.bend as V
import ./Common.bend as C
import ./LocalHistory.bend as J


def delivery(+position: J.Position, +mode: Bool, +code: String, +after: E.Snapshot, outcome: E.Outcome,
  +bytes: List<&2, U32>, +closes: Bool, +send: V.SendReturn) -> J.CallSound(position, C.delivery(mode, code, after, outcome, bytes, closes, send), after):
  match send:
    case V.SendPending{}: J.no_events(position, after)
    case V.SendComplete{}:
      J.quiet_all(position, C.core(mode, code, Route.render_delivery(E.database(after), bytes, closes, Route.Complete{False{}})), after,
        J.core_quiet(mode, code, Route.render_delivery(E.database(after), bytes, closes, Route.Complete{False{}})))
    case V.SendInterrupted{+prefix}:
      J.quiet_all(position, C.core(mode, code, Route.render_delivery(E.database(after), bytes, closes, Route.Broken{prefix})), after,
        J.core_quiet(mode, code, Route.render_delivery(E.database(after), bytes, closes, Route.Broken{prefix})))


def error_framed(+position: J.Position, +mode: Bool, +code: String, +before: E.Snapshot, +status: S.Status,
  +closes: Bool, +send: V.SendReturn, +frame: Maybe<&2, List<&2, U32>>) -> J.CallSound(position, C.error_framed(mode, code, before, status, closes, send, frame), before):
  match frame:
    case None{}: J.no_events(position, before)
    case Some{+bytes}:
      J.prefix_call(position, C.core(mode, code, [Q.Prepared{S.response_error(status), bytes}, Q.Completed{S.response_error(status), E.database(before), closes}]),
        C.delivery(mode, code, before, E.Transaction{S.response_error(status)}, bytes, closes, send), before,
        J.core_quiet(mode, code, [Q.Prepared{S.response_error(status), bytes}, Q.Completed{S.response_error(status), E.database(before), closes}]),
        delivery(position, mode, code, before, E.Transaction{S.response_error(status)}, bytes, closes, send))


def error(+position: J.Position, +mode: Bool, +code: String, +before: E.Snapshot, +status: S.Status,
  +closes: Bool, +send: V.SendReturn) -> J.CallSound(position, C.error(mode, code, before, status, closes, send), before):
  error_framed(position, mode, code, before, status, closes, send, P.frame(S.response_value(S.response_error(status))))


def failed(+position: J.Position, +mode: Bool, +code: String, +before: E.Snapshot,
  +stage: X.Stage, +identifier: String, fatal: Bool, +send: V.SendReturn) -> J.CallSound(position, C.failed(mode, code, before, stage, identifier, fatal, send), before):
  match fatal:
    case True{}:
      J.quiet_all(position, C.core(mode, code, [Q.Failed{stage, identifier, True{}}, Q.Closed{}]), before,
        J.core_quiet(mode, code, [Q.Failed{stage, identifier, True{}}, Q.Closed{}]))
    case False{}:
      J.prefix_call(position, C.core(mode, code, [Q.Failed{stage, identifier, False{}}]), C.error(mode, code, before, S.Failure{}, False{}, send), before,
        J.core_quiet(mode, code, [Q.Failed{stage, identifier, False{}}]), error(position, mode, code, before, S.Failure{}, False{}, send))
