# Error and incomplete preparation paths preserve the COMPLETE selected
# snapshot. The caller separately supplies actual primitive failure evidence;
# these equalities are derived effects, never primitive error postconditions.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/PreparedLaws.bend as H
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/PreparedRegistry.bend as G
import ../../../contract/Protocol.bend as P
import ../../../contract/Resources.bend as X
import ../../../contract/Semantics.bend as S
import ../specification/ServiceLaws.bend as E
import ./PreparePhases.bend as V

law prefixing_an_event_preserves_the_actual_snapshot:
  for event: V.PreparationEvent
  for +run: V.PreparationRun
  {V.snapshot(V.push(event, run)) == V.snapshot(run) : E.Snapshot}
def prefixing_an_event_preserves_the_actual_snapshot(event, run):
  match run:
    case V.PreparationRun{events, result, snapshot, waiting, closed}: {==}

law prefixing_an_event_preserves_the_actual_control_result:
  for event: V.PreparationEvent
  for +run: V.PreparationRun
  {V.result(V.push(event, run)) == V.result(run) : Maybe<&2, H.ControlResult>}
def prefixing_an_event_preserves_the_actual_control_result(event, run):
  match run:
    case V.PreparationRun{events, result, snapshot, waiting, closed}: {==}

law every_send_return_retains_the_already_concluded_snapshot:
  for send: V.SendReturn
  for bytes: List<&2, U32>
  for completed: H.ControlResult
  for +before: E.Snapshot
  {V.snapshot(V.delivery(send, bytes, completed, before)) == before : E.Snapshot}
def every_send_return_retains_the_already_concluded_snapshot(send, bytes, completed, before):
  match send:
    case V.SendPending{}: {==}
    case V.SendComplete{}: {==}
    case V.SendInterrupted{prefix}: {==}

law every_framed_or_unframed_error_preserves_the_complete_snapshot:
  for status: S.Status
  for +before: E.Snapshot
  for send: V.SendReturn
  for frame: Maybe<&2, List<&2, U32>>
  {V.snapshot(V.error_framed(status, before, send, frame)) == before : E.Snapshot}
def every_framed_or_unframed_error_preserves_the_complete_snapshot(status, before, send, frame):
  match send frame:
    case _ None{}: {==}
    case V.SendPending{} Some{bytes}: {==}
    case V.SendComplete{} Some{bytes}: {==}
    case V.SendInterrupted{prefix} Some{bytes}: {==}

law an_error_never_replaces_the_database_or_last_response_or_registry:
  for +status: S.Status
  for +before: E.Snapshot
  for send: V.SendReturn
  {V.snapshot(V.error(status, before, send)) == before : E.Snapshot}
def an_error_never_replaces_the_database_or_last_response_or_registry(status, before, send):
  every_framed_or_unframed_error_preserves_the_complete_snapshot(status, before, send, P.frame(S.response_value(S.response_error(status))))

law a_real_primitive_failure_preserves_the_complete_snapshot:
  for +stage: X.Stage
  for +identifier: String
  for fatal: Bool
  for +before: E.Snapshot
  for +send: V.SendReturn
  {V.snapshot(V.failed(stage, identifier, fatal, before, send)) == before : E.Snapshot}
def a_real_primitive_failure_preserves_the_complete_snapshot(stage, identifier, fatal, before, send):
  match fatal:
    case True{}: {==}
    case False{}:
      Equal.trans(E.Snapshot,
        V.snapshot(V.push(V.PrimitiveFailed{stage, identifier, False{}}, V.error(S.Failure{}, before, send))),
        V.snapshot(V.error(S.Failure{}, before, send)), before,
        prefixing_an_event_preserves_the_actual_snapshot(V.PrimitiveFailed{stage, identifier, False{}}, V.error(S.Failure{}, before, send)),
        an_error_never_replaces_the_database_or_last_response_or_registry(S.Failure{}, before, send))

law failed_sealing_cannot_change_the_complete_snapshot:
  for ~c: S.Configuration
  for +stage: X.Stage
  for +identifier: String
  for +fatal: Bool
  for mode: V.Mode
  for raw: P.Request
  for +before: E.Snapshot
  for handle: String
  for bytes: List<&2, U32>
  for +send: V.SendReturn
  {V.snapshot(V.seal_result(c, V.SealFailed{stage, identifier, fatal}, mode, raw, before, handle, bytes, send)) == before : E.Snapshot}
def failed_sealing_cannot_change_the_complete_snapshot(c, stage, identifier, fatal, mode, raw, before, handle, bytes, send):
  a_real_primitive_failure_preserves_the_complete_snapshot(stage, identifier, fatal, before, send)

law receipt_limit_failure_preserves_the_complete_snapshot:
  for ~c: S.Configuration
  for mode: V.Mode
  for raw: P.Request
  for +before: E.Snapshot
  for handle: String
  for seal: V.SealReturn
  for +send: V.SendReturn
  {V.snapshot(V.receipt_fit(c, False{}, mode, raw, before, handle, seal, send)) == before : E.Snapshot}
def receipt_limit_failure_preserves_the_complete_snapshot(c, mode, raw, before, handle, seal, send):
  an_error_never_replaces_the_database_or_last_response_or_registry(S.Limit{}, before, send)

law failed_allocation_preserves_the_complete_snapshot:
  for ~c: S.Configuration
  for +stage: X.Stage
  for +identifier: String
  for +fatal: Bool
  for mode: V.Mode
  for raw: P.Request
  for +before: E.Snapshot
  for seal: V.SealReturn
  for +send: V.SendReturn
  {V.snapshot(V.allocated(c, V.AllocatorFailed{stage, identifier, fatal}, mode, raw, before, seal, send)) == before : E.Snapshot}
def failed_allocation_preserves_the_complete_snapshot(c, stage, identifier, fatal, mode, raw, before, seal, send):
  a_real_primitive_failure_preserves_the_complete_snapshot(stage, identifier, fatal, before, send)

law failed_checker_preserves_the_complete_snapshot:
  for ~c: S.Configuration
  for +stage: X.Stage
  for +identifier: String
  for +fatal: Bool
  for mode: V.Mode
  for raw: P.Request
  for context: D.Context
  for +before: E.Snapshot
  for allocation: V.AllocatorReturn
  for seal: V.SealReturn
  for +send: V.SendReturn
  {V.snapshot(V.checked(c, V.CheckerFailed{stage, identifier, fatal}, mode, raw, context, before, allocation, seal, send)) == before : E.Snapshot}
def failed_checker_preserves_the_complete_snapshot(c, stage, identifier, fatal, mode, raw, context, before, allocation, seal, send):
  a_real_primitive_failure_preserves_the_complete_snapshot(stage, identifier, fatal, before, send)

law refuted_checker_preserves_the_complete_snapshot:
  for ~c: S.Configuration
  for +mode: V.Mode
  for +raw: P.Request
  for +context: D.Context
  for +before: E.Snapshot
  for allocation: V.AllocatorReturn
  for seal: V.SealReturn
  for +send: V.SendReturn
  {V.snapshot(V.checked(c, V.CheckerRefuted{}, mode, raw, context, before, allocation, seal, send)) == before : E.Snapshot}
def refuted_checker_preserves_the_complete_snapshot(c, mode, raw, context, before, allocation, seal, send):
  Equal.trans(E.Snapshot,
    V.snapshot(V.checked(c, V.CheckerRefuted{}, mode, raw, context, before, allocation, seal, send)),
    V.snapshot(V.error(S.Certificate{}, before, send)), before,
    prefixing_an_event_preserves_the_actual_snapshot(V.Refuted{W.Extension{V.operation(mode), raw}, context}, V.error(S.Certificate{}, before, send)),
    an_error_never_replaces_the_database_or_last_response_or_registry(S.Certificate{}, before, send))
