# Actual Core.prepare feeds actual cleanup; this is not an arbitrary supplied
# Prepared packet. Nonfatal cleanup retains the first preparation and adds the
# matching Failure preparation before its one conclusion.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Semantics.bend as S
import ../../../../../src/Core.bend as Core
import ../../../../ProtocolService.bend as Q
import ../../../../RoutesService.bend as Route
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../model/EventObserver.bend as O
import ../../../model/FrameBounds.bend as B
import ../../../model/serial/Common.bend as C
import ../../../model/serial/ExecutionPhases.bend as Exec
import ../../../../../tests/proof/service-fixtures/Resolution.bend as Fixture

def bytes(value: Maybe<&2, List<&2, U32>>) -> List<&2, U32>:
  match value:
    case None{}: []
    case Some{bytes}: bytes

def response(status: S.Status) -> S.Response:
  S.Response{status, D.VAbsent{}}

def frame(status: S.Status) -> List<&2, U32>:
  bytes(P.frame(S.response_value(response(status))))

def prepared() -> Maybe<&2, Core.Prepared>:
  Core.prepare(Core.Stopped{E.database(Fixture.missing()), [], response(S.Success{})}, Fixture.configuration())

def actual(cleanup: Route.Cleanup) -> C.CallRun:
  Exec.prepared_result(True{}, "client", Fixture.missing(), prepared(), cleanup, V.SendPending{})

law actual_nonfatal_cleanup_preserves_its_earlier_success_preparation:
  {B.query(O.AuditEvent, C.events(actual(Route.ErrorCleanup{"cleanup", False{}})), 0n) ==
    Some{O.Core{True{}, "client", Q.Prepared{response(S.Success{}), frame(S.Success{})}}} : Maybe<&2, O.AuditEvent>}
def actual_nonfatal_cleanup_preserves_its_earlier_success_preparation(): {==}

law actual_nonfatal_cleanup_has_its_second_matching_failure_preparation:
  {B.query(O.AuditEvent, C.events(actual(Route.ErrorCleanup{"cleanup", False{}})), 2n) ==
    Some{O.Core{True{}, "client", Q.Prepared{response(S.Failure{}), frame(S.Failure{})}}} : Maybe<&2, O.AuditEvent>}
def actual_nonfatal_cleanup_has_its_second_matching_failure_preparation(): {==}

law actual_nonfatal_cleanup_has_exactly_its_failure_conclusion_after_both_preparations:
  {B.query(O.AuditEvent, C.events(actual(Route.ErrorCleanup{"cleanup", False{}})), 3n) ==
    Some{O.Core{True{}, "client", Q.Completed{response(S.Failure{}), E.database(Fixture.missing()), False{}}}} : Maybe<&2, O.AuditEvent>}
def actual_nonfatal_cleanup_has_exactly_its_failure_conclusion_after_both_preparations(): {==}
