# No unselected framing/EOF block may continue using the same ordinal. This
# derives from actual reception dispatch and delivery flags, not no-duplicates.
import Base
import ../../../../contract/Logic.bend as L
import ../../../../contract/Protocol.bend as P
import ../../../../contract/Resources.bend as X
import ../../../../contract/Semantics.bend as S
import ../../../SourceService.bend as Source
import ../../specification/ServiceLaws.bend as E
import ../../phases/PreparePhases.bend as V
import ../EventObserver.bend as O
import ./Common.bend as C
import ./Decode.bend as Decode
import ./Dispatch.bend as Dispatch
import ./Engine.bend as Engine


def prefixed_continues(prefix: List<&2, O.AuditEvent>, run: C.CallRun) ->
  {C.continues(C.prefix(prefix, run)) == C.continues(run) : Bool}:
  C.CallRun{events, snapshot, outcome, waiting, closed} = run
  {==}


def closed_error_framed(mode: Bool, code: String, before: E.Snapshot, status: S.Status,
  send: V.SendReturn, frame: Maybe<&2, List<&2, U32>>) ->
  {C.continues(C.error_framed(mode, code, before, status, True{}, send, frame)) == False{} : Bool}:
  match send frame:
    case V.SendPending{} None{}: {==}
    case V.SendPending{} Some{bytes}: {==}
    case V.SendComplete{} None{}: {==}
    case V.SendComplete{} Some{bytes}: {==}
    case V.SendInterrupted{prefix} None{}: {==}
    case V.SendInterrupted{prefix} Some{bytes}: {==}


def closed_error(mode: Bool, code: String, before: E.Snapshot, +status: S.Status, send: V.SendReturn) ->
  {C.continues(C.error(mode, code, before, status, True{}, send)) == False{} : Bool}:
  closed_error_framed(mode, code, before, status, send, P.frame(S.response_value(S.response_error(status))))


def disposed_is_selected_or_terminal(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +before: E.Snapshot, +disposition: X.Disposition, +primitives: Dispatch.Primitives) ->
  L.Disjunction<{Engine.selection(disposition) == True{} : Bool},
    {C.continues(Dispatch.decoded(c, binding, public, before, Decode.disposed(c, E.database(before), disposition), primitives)) == False{} : Bool}>:
  match disposition:
    case X.CloseWithoutResponse{}: L.Right{{==}}
    case X.RefuseContinue{status}: L.Left{{==}}
    case X.ProcessBody{bytes}: L.Left{{==}}
    case X.RefuseClose{+status}:
      L.Right{Equal.trans(Bool,
        C.continues(C.prefix(Nil{}, C.error(False{}, "", before, status, True{}, Dispatch.send(primitives)))),
        C.continues(C.error(False{}, "", before, status, True{}, Dispatch.send(primitives))), False{},
        prefixed_continues(Nil{}, C.error(False{}, "", before, status, True{}, Dispatch.send(primitives))),
        closed_error(False{}, "", before, status, Dispatch.send(primitives)))}


law every_actual_serial_block_is_selected_or_stops_further_selection:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +before: E.Snapshot
  for +input: X.Reception
  for +primitives: Dispatch.Primitives
  L.Disjunction<{Engine.selection(X.decide_reception(c, input)) == True{} : Bool},
    {C.continues(Dispatch.run(c, binding, public, before, input, primitives)) == False{} : Bool}>
def every_actual_serial_block_is_selected_or_stops_further_selection(c, binding, public, before, input, primitives):
  disposed_is_selected_or_terminal(c, binding, public, before, X.decide_reception(c, input), primitives)
