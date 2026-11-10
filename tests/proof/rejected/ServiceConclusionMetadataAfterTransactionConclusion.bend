import Base
import ../../../contract/Data.bend as D
import ../../../contract/PreparedLaws.bend as H
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/Semantics.bend as S
import ../../../proof/ProtocolService.bend as Q
import ../../../proof/service/specification/ServiceLaws.bend as E
import ../../../proof/service/phases/PreparePhases.bend as V
import ../../../proof/service/model/EventObserver.bend as O
import ../../../proof/service/model/serial/Common.bend as C
import ../../../proof/service/laws/serial/core-conclusions/Meaning.bend as M

def snapshot() -> E.Snapshot: E.Snapshot{"fixture", D.State{[], []}, [], []}
def response(status: S.Status) -> S.Response: S.Response{status, D.VAbsent{}}
def prep(+status: S.Status, bytes: List<&2, U32>) -> O.AuditEvent: O.Core{True{}, "client", Q.Prepared{response(status), bytes}}
def done(+status: S.Status, closes: Bool) -> O.AuditEvent: O.Core{True{}, "client", Q.Completed{response(status), E.database(snapshot()), closes}}

def false_negative_MetadataAfterTransactionConclusion() -> M.Shape<C.append([prep(S.Failure{}, [0])], Con{done(S.Failure{}, False{}), [O.Preparation{V.ReceiptConcluded{W.InvalidatedReceipt{}, H.ControlResult{E.database(snapshot()), [], H.Metadata{W.InvalidatedReceipt{}}}, snapshot(), False{}}}]})>:
  M.TransactionShape{[prep(S.Failure{}, [0])], [O.Preparation{V.ReceiptConcluded{W.InvalidatedReceipt{}, H.ControlResult{E.database(snapshot()), [], H.Metadata{W.InvalidatedReceipt{}}}, snapshot(), False{}}}], done(S.Failure{}, False{}), response(S.Failure{}), E.database(snapshot()), [0], 0n, prep(S.Failure{}, [0]),
    {==},
    {==},
    {==},
    {==},
    {==},
    {==}}
