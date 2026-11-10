# Independent occurrence meaning for conclusions. A nonempty shape identifies
# its literal source prefix/head/suffix and excludes every OTHER prepared
# transaction OR metadata conclusion. Transaction evidence requires a real
# earlier Prepared occurrence with the same response; Prepared is not unique.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/PreparedLaws.bend as H
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/Semantics.bend as S
import ../../../../ProtocolService.bend as Q
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../phases/InvalidationPhases.bend as N
import ../../../model/EventObserver.bend as O
import ../../../model/FrameBounds.bend as B
import ../../../model/serial/Common.bend as C

type Endpoint is Data:
  Transaction{response: S.Response, state: D.State, closes: Bool}
  Metadata{receipt: W.Receipt, result: H.ControlResult, snapshot: E.Snapshot, closes: Bool}

type Framing is Data:
  Framing{response: S.Response, bytes: List<&2, U32>}

def completed_endpoint(mode: Bool, response: S.Response, state: D.State, closes: Bool) -> Maybe<&2, Endpoint>:
  match mode:
    case False{}: None{}
    case True{}: Some{Transaction{response, state, closes}}

def frame_end(mode: Bool, frame: Q.Frame) -> Maybe<&2, Endpoint>:
  match frame:
    case Q.Completed{response, state, closes}: completed_endpoint(mode, response, state, closes)
    case _: None{}

def phase_end(phase: V.PreparationEvent) -> Maybe<&2, Endpoint>:
  match phase:
    case V.ErrorConcluded{status, snapshot, closes}: Some{Transaction{S.response_error(status), E.database(snapshot), closes}}
    case V.ReceiptConcluded{receipt, result, snapshot, closes}: Some{Metadata{receipt, result, snapshot, closes}}
    case _: None{}

def invalidation_end(phase: N.InvalidationEvent) -> Maybe<&2, Endpoint>:
  match phase:
    case N.InvalidationBase{base}: phase_end(base)
    case N.RegistryRemoved{handle, before, after}: None{}

def endpoint(event: O.AuditEvent) -> Maybe<&2, Endpoint>:
  match event:
    case O.Core{mode, code, frame}: frame_end(mode, frame)
    case O.BoundCore{mode, origin, frame}: frame_end(mode, frame)
    case O.Preparation{phase}: phase_end(phase)
    case O.Invalidation{phase}: invalidation_end(phase)
    case _: None{}

def prepared_framing(mode: Bool, response: S.Response, bytes: List<&2, U32>) -> Maybe<&2, Framing>:
  match mode:
    case False{}: None{}
    case True{}: Some{Framing{response, bytes}}

def frame_prepared(mode: Bool, frame: Q.Frame) -> Maybe<&2, Framing>:
  match frame:
    case Q.Prepared{response, bytes}: prepared_framing(mode, response, bytes)
    case _: None{}

def phase_prepared(phase: V.PreparationEvent) -> Maybe<&2, Framing>:
  match phase:
    case V.ErrorPrepared{status, bytes}: Some{Framing{S.response_error(status), bytes}}
    case _: None{}

def invalidation_prepared(phase: N.InvalidationEvent) -> Maybe<&2, Framing>:
  match phase:
    case N.InvalidationBase{base}: phase_prepared(base)
    case N.RegistryRemoved{handle, before, after}: None{}

def prepared(event: O.AuditEvent) -> Maybe<&2, Framing>:
  match event:
    case O.Core{mode, code, frame}: frame_prepared(mode, frame)
    case O.BoundCore{mode, origin, frame}: frame_prepared(mode, frame)
    case O.Preparation{phase}: phase_prepared(phase)
    case O.Invalidation{phase}: invalidation_prepared(phase)
    case _: None{}

def absent(value: Maybe<&2, Endpoint>) -> Bool:
  match value:
    case None{}: True{}
    case Some{endpoint}: False{}

def quiet(events: List<&2, O.AuditEvent>) -> Bool:
  match events:
    case Nil{}: True{}
    case Con{event, rest}: absent(endpoint(event)) && quiet(rest)

type Shape<-events: List<&2, O.AuditEvent>> is Data:
  Quiet{excluded: {quiet(events) == True{} : Bool}}
  TransactionShape{prefix: List<&2, O.AuditEvent>, suffix: List<&2, O.AuditEvent>, event: O.AuditEvent,
    response: S.Response, state: D.State, bytes: List<&2, U32>, prepared_at: Nat, prepared_event: O.AuditEvent,
    layout: {events == C.append(prefix, Con{event, suffix}) : List<&2, O.AuditEvent>},
    concluded: {endpoint(event) == Some{Transaction{response, state, False{}}} : Maybe<&2, Endpoint>},
    prefix_quiet: {quiet(prefix) == True{} : Bool}, suffix_quiet: {quiet(suffix) == True{} : Bool},
    prepared_query: {B.query(O.AuditEvent, prefix, prepared_at) == Some{prepared_event} : Maybe<&2, O.AuditEvent>},
    prepared_payload: {prepared(prepared_event) == Some{Framing{response, bytes}} : Maybe<&2, Framing>}}
  MetadataShape{prefix: List<&2, O.AuditEvent>, suffix: List<&2, O.AuditEvent>, event: O.AuditEvent,
    receipt: W.Receipt, result: H.ControlResult, snapshot: E.Snapshot, closes: Bool,
    layout: {events == C.append(prefix, Con{event, suffix}) : List<&2, O.AuditEvent>},
    concluded: {endpoint(event) == Some{Metadata{receipt, result, snapshot, closes}} : Maybe<&2, Endpoint>},
    prefix_quiet: {quiet(prefix) == True{} : Bool}, suffix_quiet: {quiet(suffix) == True{} : Bool}}
