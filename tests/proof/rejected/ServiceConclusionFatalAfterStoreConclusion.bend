import Base
import ../../../contract/Data.bend as D
import ../../../contract/Resources.bend as X
import ../../../contract/Semantics.bend as S
import ../../../proof/ProtocolService.bend as Q
import ../../../proof/RoutesService.bend as Route
import ../../../proof/service/specification/ServiceLaws.bend as E
import ../../../proof/service/model/EventObserver.bend as O
import ../../../proof/service/model/FrameBounds.bend as B
import ../../../proof/service/model/serial/Common.bend as C
import ../../../proof/service/laws/serial/core-conclusions/CleanupExamples.bend as Cleanup
import ../service-fixtures/Resolution.bend as Fixture

def snapshot() -> E.Snapshot: E.Snapshot{"fixture", D.State{[], []}, [], []}
def response(status: S.Status) -> S.Response: S.Response{status, D.VAbsent{}}
def prep(+status: S.Status, bytes: List<&2, U32>) -> O.AuditEvent: O.Core{True{}, "client", Q.Prepared{response(status), bytes}}
def done(+status: S.Status, closes: Bool) -> O.AuditEvent: O.Core{True{}, "client", Q.Completed{response(status), E.database(snapshot()), closes}}

def false_negative_FatalAfterStoreConclusion() -> {B.query(O.AuditEvent, C.events(Cleanup.actual(Route.FatalAfterStore{X.Prepare{}, "fatal"})), 3n) == Some{O.Core{True{}, "client", Q.Completed{Cleanup.response(S.Success{}), E.database(Fixture.missing()), False{}}}} : Maybe<&2, O.AuditEvent>}:
  {==}
