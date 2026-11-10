# The explicit publication payload is determined by the ACTUAL conclusion
# renderer, including fatal post-store cleanup. No result validity is assumed.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Logic.bend as L
import ../../../../contract/Resources.bend as X
import ../../../../contract/Semantics.bend as S
import ../../../../src/Core.bend as Core
import ../../../Foundations.bend as F
import ../../../ProtocolService.bend as Q
import ../../../RoutesService.bend as Route
import ../../specification/ServiceLaws.bend as E
import ../../phases/PreparePhases.bend as V
import ../EventObserver.bend as O
import ../FrameBounds.bend as B
import ./Common.bend as C
import ./ExecutionPhases.bend as Exec
import ./PublicationAuthority.bend as Authority


def Actual(-mode: Bool, -before: E.Snapshot, -conclusion: Core.Conclusion, event: O.AuditEvent) -> Type:
  match event:
    case O.Publication{actual_mode, response, bytes, actual_before, after}:
      L.E<{actual_mode == mode : Bool}, L.E<{Core.Conclusion{E.database(after), response, bytes} == conclusion : Core.Conclusion},
        L.E<{actual_before == before : E.Snapshot}, {Authority.response_status(response) == S.Success{} : S.Status}>>>
    case _: Unit


def All(-mode: Bool, -before: E.Snapshot, -conclusion: Core.Conclusion, events: List<&2, O.AuditEvent>) -> Type:
  match events:
    case Nil{}: Unit
    case Con{event, rest}: L.E<Actual(mode, before, conclusion, event), All(mode, before, conclusion, rest)>


def append(-mode: Bool, -before: E.Snapshot, -conclusion: Core.Conclusion, +prefix: List<&2, O.AuditEvent>, +suffix: List<&2, O.AuditEvent>, own: All(mode, before, conclusion, prefix), following: All(mode, before, conclusion, suffix)) -> All(mode, before, conclusion, C.append(prefix, suffix)):
  match prefix own:
    case Nil{} _: following
    case Con{head, rest} L.Both{first, later}: L.Both{first, append(mode, before, conclusion, rest, suffix, later, following)}


def core(-mode: Bool, -before: E.Snapshot, -conclusion: Core.Conclusion, +actual_mode: Bool, +code: String, frames: List<&2, Q.Frame>) -> All(mode, before, conclusion, C.core(actual_mode, code, frames)):
  match frames:
    case Nil{}: Unit{}
    case Con{frame, rest}: L.Both{Unit{}, core(mode, before, conclusion, actual_mode, code, rest)}


def prefix(-mode: Bool, -before: E.Snapshot, -conclusion: Core.Conclusion, +events: List<&2, O.AuditEvent>, run: C.CallRun,
  own: All(mode, before, conclusion, events), following: All(mode, before, conclusion, C.events(run))) -> All(mode, before, conclusion, C.events(C.prefix(events, run))):
  match run:
    case C.CallRun{suffix, snapshot, result, waiting, closed}: append(mode, before, conclusion, events, suffix, own, following)


def delivery(-mode: Bool, -before: E.Snapshot, -conclusion: Core.Conclusion, +actual_mode: Bool, +code: String, +after: E.Snapshot, result: E.Outcome, +bytes: List<&2, U32>, +closes: Bool, send: V.SendReturn) -> All(mode, before, conclusion, C.events(C.delivery(actual_mode, code, after, result, bytes, closes, send))):
  match send:
    case V.SendPending{}: Unit{}
    case V.SendComplete{}: core(mode, before, conclusion, actual_mode, code, Route.render_delivery(E.database(after), bytes, closes, Route.Complete{False{}}))
    case V.SendInterrupted{interrupted}: core(mode, before, conclusion, actual_mode, code, Route.render_delivery(E.database(after), bytes, closes, Route.Broken{interrupted}))


def publication(+mode: Bool, +before: E.Snapshot, +state: D.State, response: S.Response, +bytes: List<&2, U32>) ->
  All(mode, before, Core.Conclusion{state, response, bytes}, Exec.publication(mode, before, Exec.published(before, Core.Conclusion{state, response, bytes}), response, bytes)):
  match response:
    case S.Response{S.Success{}, value}: L.Both{L.Both{{==}, L.Both{{==}, L.Both{{==}, {==}}}}, Unit{}}
    case S.Response{S.Refusal{}, value}: Unit{}
    case S.Response{S.Input{}, value}: Unit{}
    case S.Response{S.Authentication{}, value}: Unit{}
    case S.Response{S.Certificate{}, value}: Unit{}
    case S.Response{S.DataError{}, value}: Unit{}
    case S.Response{S.Limit{}, value}: Unit{}
    case S.Response{S.Failure{}, value}: Unit{}


law every_actual_concluded_publication_preserves_its_exact_conclusion_payload:
  for +mode: Bool
  for +code: String
  for +before: E.Snapshot
  for conclusion: Core.Conclusion
  for +send: V.SendReturn
  All(mode, before, conclusion, C.events(Exec.concluded(mode, code, before, conclusion, send)))
def every_actual_concluded_publication_preserves_its_exact_conclusion_payload(mode, code, before, conclusion, send):
  match conclusion:
    case Core.Conclusion{+state, +response, +bytes}:
      +conclusion: Core.Conclusion = Core.Conclusion{state, response, bytes}
      +after: E.Snapshot = Exec.published(before, conclusion)
      prefix(mode, before, conclusion, C.append([O.Core{mode, code, Q.Prepared{response, bytes}}], C.append(Exec.publication(mode, before, after, response, bytes), [O.Core{mode, code, Q.Completed{response, E.database(after), False{}}}])),
        C.delivery(mode, code, after, E.Transaction{response}, bytes, False{}, send), L.Both{Unit{}, append(mode, before, conclusion, Exec.publication(mode, before, after, response, bytes), [O.Core{mode, code, Q.Completed{response, E.database(after), False{}}}],
          publication(mode, before, state, response, bytes), L.Both{Unit{}, Unit{}})}, delivery(mode, before, conclusion, mode, code, after, E.Transaction{response}, bytes, False{}, send))


law every_actual_fatal_post_store_publication_preserves_its_exact_conclusion_payload:
  for +mode: Bool
  for +code: String
  for +before: E.Snapshot
  for conclusion: Core.Conclusion
  for +stage: X.Stage
  for +identifier: String
  All(mode, before, conclusion, C.events(Exec.fatal_after_store(mode, code, before, conclusion, stage, identifier)))
def every_actual_fatal_post_store_publication_preserves_its_exact_conclusion_payload(mode, code, before, conclusion, stage, identifier):
  match conclusion:
    case Core.Conclusion{+state, +response, +bytes}:
      +conclusion: Core.Conclusion = Core.Conclusion{state, response, bytes}
      +after: E.Snapshot = Exec.published(before, conclusion)
      L.Both{Unit{}, append(mode, before, conclusion, Exec.publication(mode, before, after, response, bytes), C.core(mode, code, [Q.Failed{stage, identifier, True{}}, Q.Closed{}]),
        publication(mode, before, state, response, bytes), L.Both{Unit{}, L.Both{Unit{}, Unit{}}})}


def query(-mode: Bool, -before: E.Snapshot, -conclusion: Core.Conclusion, events: List<&2, O.AuditEvent>, index: Nat, +event: O.AuditEvent, all: All(mode, before, conclusion, events),
  found: {B.query(O.AuditEvent, events, index) == Some{event} : Maybe<&2, O.AuditEvent>}) -> Actual(mode, before, conclusion, event):
  match events index all:
    case Nil{} _ _: L.ex_false(Actual(mode, before, conclusion, event), F.none_negative_some(O.AuditEvent, event, found))
    case Con{+head, rest} 0n L.Both{first, later}:
      %F.some_injective(O.AuditEvent, head, event, found) : Actual(mode, before, conclusion, _) first
    case Con{head, rest} 1n+k L.Both{first, later}: query(mode, before, conclusion, rest, k, event, later, found)
