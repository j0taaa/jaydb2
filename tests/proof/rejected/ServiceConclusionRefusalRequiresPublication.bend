import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../src/Core.bend as Core
import ../../../proof/ProtocolService.bend as Q
import ../../../proof/service/specification/ServiceLaws.bend as E
import ../../../proof/service/phases/PreparePhases.bend as V
import ../../../proof/service/model/EventObserver.bend as O
import ../../../proof/service/model/FrameBounds.bend as B
import ../../../proof/service/model/serial/Common.bend as C
import ../../../proof/service/model/serial/ExecutionPhases.bend as Exec

def snapshot() -> E.Snapshot: E.Snapshot{"fixture", D.State{[], []}, [], []}
def response(status: S.Status) -> S.Response: S.Response{status, D.VAbsent{}}
def prep(+status: S.Status, bytes: List<&2, U32>) -> O.AuditEvent: O.Core{True{}, "client", Q.Prepared{response(status), bytes}}
def done(+status: S.Status, closes: Bool) -> O.AuditEvent: O.Core{True{}, "client", Q.Completed{response(status), E.database(snapshot()), closes}}

def false_negative_RefusalRequiresPublication() -> {B.query(O.AuditEvent, C.events(Exec.concluded(True{}, "client", snapshot(), Core.Conclusion{E.database(snapshot()), response(S.Refusal{}), [0]}, V.SendPending{})), 1n) == Some{O.Publication{True{}, response(S.Refusal{}), [0], snapshot(), snapshot()}} : Maybe<&2, O.AuditEvent>}:
  {==}
