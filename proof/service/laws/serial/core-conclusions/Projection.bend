# Faithful independent endpoint/framing projections of ALL actual audit event
# constructors. Publication cofacts stay present; none is a conclusion.
import Base
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/Semantics.bend as S
import ../../../../Foundations.bend as F
import ../../../../ProtocolService.bend as Q
import ../../../../SourceService.bend as Source
import ../../../../HostTransitions.bend as Host
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../phases/InvalidationPhases.bend as N
import ../../../model/EventObserver.bend as O
import ../../../model/ObservationUniqueness.bend as U
import ./Meaning.bend as M

def normalized(view: U.View) -> Maybe<&2, U.View>:
  match view:
    case U.ConclusionView{outcome, state, closes}: Some{U.ConclusionView{outcome, state, closes}}
    case _: None{}

def endpoint_view(endpoint: Maybe<&2, M.Endpoint>) -> Maybe<&2, U.View>:
  match endpoint:
    case None{}: None{}
    case Some{M.Transaction{response, state, closes}}: Some{U.ConclusionView{E.Transaction{response}, state, closes}}
    case Some{M.Metadata{receipt, result, snapshot, closes}}: Some{U.ConclusionView{E.Receipt{receipt}, E.database(snapshot), closes}}

def frame_endpoint(~c: S.Configuration, -program: S.Program, mode: Bool, frame: Q.Frame) ->
  {normalized(U.view(E.core_fact(mode, Q.fact_of_frame(c, program, frame)))) == endpoint_view(M.frame_end(mode, frame)) : Maybe<&2, U.View>}:
  match mode frame:
    case False{} Q.Configured{}: {==}
    case False{} Q.InitialAccepts{}: {==}
    case False{} Q.Initialized{state}: {==}
    case False{} Q.InitialRefused{status}: {==}
    case False{} Q.Encoded{value, bytes}: {==}
    case False{} Q.Decoded{bytes, value}: {==}
    case False{} Q.Stored{state, bytes, abstraction}: {==}
    case False{} Q.Checked{position, count}: {==}
    case False{} Q.Constructed{position, count}: {==}
    case False{} Q.Read{before, count, declared}: {==}
    case False{} Q.Received{request}: {==}
    case False{} Q.Authenticated{request, context}: {==}
    case False{} Q.Accepts{request, context}: {==}
    case False{} Q.Rejected{request, context}: {==}
    case False{} Q.Started{request, context}: {==}
    case False{} Q.Evaluated{request, context, execution_trace}: {==}
    case False{} Q.Operated{schema, state, operation, result}: {==}
    case False{} Q.Prepared{response, bytes}: {==}
    case False{} Q.Published{state}: {==}
    case False{} Q.Visible{state}: {==}
    case False{} Q.Failed{stage, identifier, fatal}: {==}
    case False{} Q.Completed{response, state, closes}: {==}
    case False{} Q.Delivered{bytes}: {==}
    case False{} Q.Interrupted{prefix}: {==}
    case False{} Q.Closed{}: {==}
    case False{} Q.Next{previous, initial}: {==}
    case False{} Q.Inspection{description}: {==}
    case False{} Q.Effect{description}: {==}
    case True{} Q.Configured{}: {==}
    case True{} Q.InitialAccepts{}: {==}
    case True{} Q.Initialized{state}: {==}
    case True{} Q.InitialRefused{status}: {==}
    case True{} Q.Encoded{value, bytes}: {==}
    case True{} Q.Decoded{bytes, value}: {==}
    case True{} Q.Stored{state, bytes, abstraction}: {==}
    case True{} Q.Checked{position, count}: {==}
    case True{} Q.Constructed{position, count}: {==}
    case True{} Q.Read{before, count, declared}: {==}
    case True{} Q.Received{request}: {==}
    case True{} Q.Authenticated{request, context}: {==}
    case True{} Q.Accepts{request, context}: {==}
    case True{} Q.Rejected{request, context}: {==}
    case True{} Q.Started{request, context}: {==}
    case True{} Q.Evaluated{request, context, execution_trace}: {==}
    case True{} Q.Operated{schema, state, operation, result}: {==}
    case True{} Q.Prepared{response, bytes}: {==}
    case True{} Q.Published{state}: {==}
    case True{} Q.Visible{state}: {==}
    case True{} Q.Failed{stage, identifier, fatal}: {==}
    case True{} Q.Completed{response, state, closes}: {==}
    case True{} Q.Delivered{bytes}: {==}
    case True{} Q.Interrupted{prefix}: {==}
    case True{} Q.Closed{}: {==}
    case True{} Q.Next{previous, initial}: {==}
    case True{} Q.Inspection{description}: {==}
    case True{} Q.Effect{description}: {==}

def phase_endpoint(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, phase: V.PreparationEvent) ->
  {normalized(U.view(V.fact(c, binding, public, phase))) == endpoint_view(M.phase_end(phase)) : Maybe<&2, U.View>}:
  match phase:
    case V.WireReceived{wire}: {==}
    case V.IdentityEstablished{wire, context}: {==}
    case V.Accepted{wire, context}: {==}
    case V.Refuted{wire, context}: {==}
    case V.PrimitiveFailed{stage, identifier, fatal}: {==}
    case V.HandleChosen{handle}: {==}
    case V.ReceiptPrepared{receipt, bytes}: {==}
    case V.ArtifactSealed{entry}: {==}
    case V.RegistryChanged{entry, before, after}: {==}
    case V.ReceiptConcluded{receipt, result, snapshot, closes}: {==}
    case V.ErrorPrepared{status, bytes}: {==}
    case V.ErrorConcluded{status, snapshot, closes}: {==}
    case V.Delivered{bytes}: {==}
    case V.Interrupted{prefix}: {==}
    case V.Closed{}: {==}

def invalidation_endpoint(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, phase: N.InvalidationEvent) ->
  {normalized(U.view(N.fact(c, binding, public, phase))) == endpoint_view(M.invalidation_end(phase)) : Maybe<&2, U.View>}:
  match phase:
    case N.InvalidationBase{base}: phase_endpoint(c, binding, public, base)
    case N.RegistryRemoved{handle, before, after}: {==}

def event_endpoint(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, event: O.AuditEvent) ->
  {normalized(U.view(O.fact(c, binding, public, event))) == endpoint_view(M.endpoint(event)) : Maybe<&2, U.View>}:
  match event:
    case O.Core{mode, code, frame}: frame_endpoint(c, Source.program(binding, Host.origin(public, code)), mode, frame)
    case O.BoundCore{mode, origin, frame}: frame_endpoint(c, Source.program(binding, origin), mode, frame)
    case O.Preparation{phase}: phase_endpoint(c, binding, public, phase)
    case O.Invalidation{phase}: invalidation_endpoint(c, binding, public, phase)
    case O.Selection{snapshot}: {==}
    case O.Resolution{raw, entry, context}: {==}
    case O.Publication{mode, response, bytes, before, after}: {==}

def framing_fact(framing: M.Framing) -> E.Fact:
  match framing:
    case M.Framing{response, bytes}: E.PreparedKernel{I.Prepared{response, bytes}}

def no_prepared(-fact: E.Fact, -response: S.Response, -bytes: List<&2, U32>,
  impossible: {None{} == Some{M.Framing{response, bytes}} : Maybe<&2, M.Framing>}) ->
  {fact == E.PreparedKernel{I.Prepared{response, bytes}} : E.Fact}:
  L.ex_false({fact == E.PreparedKernel{I.Prepared{response, bytes}} : E.Fact}, F.none_negative_some(M.Framing, M.Framing{response, bytes}, impossible))

def frame_prepared(~c: S.Configuration, -program: S.Program, mode: Bool, frame: Q.Frame, +response: S.Response, +bytes: List<&2, U32>,
  actual: {M.frame_prepared(mode, frame) == Some{M.Framing{response, bytes}} : Maybe<&2, M.Framing>}) ->
  {E.core_fact(mode, Q.fact_of_frame(c, program, frame)) == E.PreparedKernel{I.Prepared{response, bytes}} : E.Fact}:
  match mode frame:
    case False{} Q.Configured{}: no_prepared(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Configured{})), response, bytes, actual)
    case False{} Q.InitialAccepts{}: no_prepared(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.InitialAccepts{})), response, bytes, actual)
    case False{} Q.Initialized{field_state}: no_prepared(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Initialized{field_state})), response, bytes, actual)
    case False{} Q.InitialRefused{field_status}: no_prepared(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.InitialRefused{field_status})), response, bytes, actual)
    case False{} Q.Encoded{field_value, field_bytes}: no_prepared(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Encoded{field_value, field_bytes})), response, bytes, actual)
    case False{} Q.Decoded{field_bytes, field_value}: no_prepared(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Decoded{field_bytes, field_value})), response, bytes, actual)
    case False{} Q.Stored{field_state, field_bytes, field_abstraction}: no_prepared(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Stored{field_state, field_bytes, field_abstraction})), response, bytes, actual)
    case False{} Q.Checked{field_position, field_count}: no_prepared(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Checked{field_position, field_count})), response, bytes, actual)
    case False{} Q.Constructed{field_position, field_count}: no_prepared(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Constructed{field_position, field_count})), response, bytes, actual)
    case False{} Q.Read{field_before, field_count, field_declared}: no_prepared(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Read{field_before, field_count, field_declared})), response, bytes, actual)
    case False{} Q.Received{field_request}: no_prepared(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Received{field_request})), response, bytes, actual)
    case False{} Q.Authenticated{field_request, field_context}: no_prepared(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Authenticated{field_request, field_context})), response, bytes, actual)
    case False{} Q.Accepts{field_request, field_context}: no_prepared(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Accepts{field_request, field_context})), response, bytes, actual)
    case False{} Q.Rejected{field_request, field_context}: no_prepared(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Rejected{field_request, field_context})), response, bytes, actual)
    case False{} Q.Started{field_request, field_context}: no_prepared(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Started{field_request, field_context})), response, bytes, actual)
    case False{} Q.Evaluated{field_request, field_context, field_execution_trace}: no_prepared(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Evaluated{field_request, field_context, field_execution_trace})), response, bytes, actual)
    case False{} Q.Operated{field_schema, field_state, field_operation, field_result}: no_prepared(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Operated{field_schema, field_state, field_operation, field_result})), response, bytes, actual)
    case False{} Q.Prepared{field_response, field_bytes}: no_prepared(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Prepared{field_response, field_bytes})), response, bytes, actual)
    case False{} Q.Published{field_state}: no_prepared(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Published{field_state})), response, bytes, actual)
    case False{} Q.Visible{field_state}: no_prepared(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Visible{field_state})), response, bytes, actual)
    case False{} Q.Failed{field_stage, field_identifier, field_fatal}: no_prepared(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Failed{field_stage, field_identifier, field_fatal})), response, bytes, actual)
    case False{} Q.Completed{field_response, field_state, field_closes}: no_prepared(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Completed{field_response, field_state, field_closes})), response, bytes, actual)
    case False{} Q.Delivered{field_bytes}: no_prepared(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Delivered{field_bytes})), response, bytes, actual)
    case False{} Q.Interrupted{field_prefix}: no_prepared(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Interrupted{field_prefix})), response, bytes, actual)
    case False{} Q.Closed{}: no_prepared(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Closed{})), response, bytes, actual)
    case False{} Q.Next{field_previous, field_initial}: no_prepared(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Next{field_previous, field_initial})), response, bytes, actual)
    case False{} Q.Inspection{field_description}: no_prepared(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Inspection{field_description})), response, bytes, actual)
    case False{} Q.Effect{field_description}: no_prepared(E.core_fact(False{}, Q.fact_of_frame(c, program, Q.Effect{field_description})), response, bytes, actual)
    case True{} Q.Configured{}: no_prepared(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Configured{})), response, bytes, actual)
    case True{} Q.InitialAccepts{}: no_prepared(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.InitialAccepts{})), response, bytes, actual)
    case True{} Q.Initialized{field_state}: no_prepared(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Initialized{field_state})), response, bytes, actual)
    case True{} Q.InitialRefused{field_status}: no_prepared(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.InitialRefused{field_status})), response, bytes, actual)
    case True{} Q.Encoded{field_value, field_bytes}: no_prepared(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Encoded{field_value, field_bytes})), response, bytes, actual)
    case True{} Q.Decoded{field_bytes, field_value}: no_prepared(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Decoded{field_bytes, field_value})), response, bytes, actual)
    case True{} Q.Stored{field_state, field_bytes, field_abstraction}: no_prepared(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Stored{field_state, field_bytes, field_abstraction})), response, bytes, actual)
    case True{} Q.Checked{field_position, field_count}: no_prepared(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Checked{field_position, field_count})), response, bytes, actual)
    case True{} Q.Constructed{field_position, field_count}: no_prepared(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Constructed{field_position, field_count})), response, bytes, actual)
    case True{} Q.Read{field_before, field_count, field_declared}: no_prepared(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Read{field_before, field_count, field_declared})), response, bytes, actual)
    case True{} Q.Received{field_request}: no_prepared(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Received{field_request})), response, bytes, actual)
    case True{} Q.Authenticated{field_request, field_context}: no_prepared(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Authenticated{field_request, field_context})), response, bytes, actual)
    case True{} Q.Accepts{field_request, field_context}: no_prepared(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Accepts{field_request, field_context})), response, bytes, actual)
    case True{} Q.Rejected{field_request, field_context}: no_prepared(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Rejected{field_request, field_context})), response, bytes, actual)
    case True{} Q.Started{field_request, field_context}: no_prepared(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Started{field_request, field_context})), response, bytes, actual)
    case True{} Q.Evaluated{field_request, field_context, field_execution_trace}: no_prepared(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Evaluated{field_request, field_context, field_execution_trace})), response, bytes, actual)
    case True{} Q.Operated{field_schema, field_state, field_operation, field_result}: no_prepared(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Operated{field_schema, field_state, field_operation, field_result})), response, bytes, actual)
    case True{} Q.Prepared{+field_response, +field_bytes}: Equal.cong(M.Framing, E.Fact, framing_fact, M.Framing{field_response, field_bytes}, M.Framing{response, bytes}, F.some_injective(M.Framing, M.Framing{field_response, field_bytes}, M.Framing{response, bytes}, actual))
    case True{} Q.Published{field_state}: no_prepared(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Published{field_state})), response, bytes, actual)
    case True{} Q.Visible{field_state}: no_prepared(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Visible{field_state})), response, bytes, actual)
    case True{} Q.Failed{field_stage, field_identifier, field_fatal}: no_prepared(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Failed{field_stage, field_identifier, field_fatal})), response, bytes, actual)
    case True{} Q.Completed{field_response, field_state, field_closes}: no_prepared(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Completed{field_response, field_state, field_closes})), response, bytes, actual)
    case True{} Q.Delivered{field_bytes}: no_prepared(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Delivered{field_bytes})), response, bytes, actual)
    case True{} Q.Interrupted{field_prefix}: no_prepared(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Interrupted{field_prefix})), response, bytes, actual)
    case True{} Q.Closed{}: no_prepared(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Closed{})), response, bytes, actual)
    case True{} Q.Next{field_previous, field_initial}: no_prepared(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Next{field_previous, field_initial})), response, bytes, actual)
    case True{} Q.Inspection{field_description}: no_prepared(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Inspection{field_description})), response, bytes, actual)
    case True{} Q.Effect{field_description}: no_prepared(E.core_fact(True{}, Q.fact_of_frame(c, program, Q.Effect{field_description})), response, bytes, actual)

def phase_prepared(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, phase: V.PreparationEvent, +response: S.Response, +bytes: List<&2, U32>,
  actual: {M.phase_prepared(phase) == Some{M.Framing{response, bytes}} : Maybe<&2, M.Framing>}) ->
  {V.fact(c, binding, public, phase) == E.PreparedKernel{I.Prepared{response, bytes}} : E.Fact}:
  match phase:
    case V.WireReceived{field_wire}: no_prepared(V.fact(c, binding, public, V.WireReceived{field_wire}), response, bytes, actual)
    case V.IdentityEstablished{field_wire, field_context}: no_prepared(V.fact(c, binding, public, V.IdentityEstablished{field_wire, field_context}), response, bytes, actual)
    case V.Accepted{field_wire, field_context}: no_prepared(V.fact(c, binding, public, V.Accepted{field_wire, field_context}), response, bytes, actual)
    case V.Refuted{field_wire, field_context}: no_prepared(V.fact(c, binding, public, V.Refuted{field_wire, field_context}), response, bytes, actual)
    case V.PrimitiveFailed{field_stage, field_identifier, field_fatal}: no_prepared(V.fact(c, binding, public, V.PrimitiveFailed{field_stage, field_identifier, field_fatal}), response, bytes, actual)
    case V.HandleChosen{field_handle}: no_prepared(V.fact(c, binding, public, V.HandleChosen{field_handle}), response, bytes, actual)
    case V.ReceiptPrepared{field_receipt, field_bytes}: no_prepared(V.fact(c, binding, public, V.ReceiptPrepared{field_receipt, field_bytes}), response, bytes, actual)
    case V.ArtifactSealed{field_entry}: no_prepared(V.fact(c, binding, public, V.ArtifactSealed{field_entry}), response, bytes, actual)
    case V.RegistryChanged{field_entry, field_before, field_after}: no_prepared(V.fact(c, binding, public, V.RegistryChanged{field_entry, field_before, field_after}), response, bytes, actual)
    case V.ReceiptConcluded{field_receipt, field_result, field_snapshot, field_closes}: no_prepared(V.fact(c, binding, public, V.ReceiptConcluded{field_receipt, field_result, field_snapshot, field_closes}), response, bytes, actual)
    case V.ErrorPrepared{+field_status, +field_bytes}: Equal.cong(M.Framing, E.Fact, framing_fact, M.Framing{S.response_error(field_status), field_bytes}, M.Framing{response, bytes}, F.some_injective(M.Framing, M.Framing{S.response_error(field_status), field_bytes}, M.Framing{response, bytes}, actual))
    case V.ErrorConcluded{field_status, field_snapshot, field_closes}: no_prepared(V.fact(c, binding, public, V.ErrorConcluded{field_status, field_snapshot, field_closes}), response, bytes, actual)
    case V.Delivered{field_bytes}: no_prepared(V.fact(c, binding, public, V.Delivered{field_bytes}), response, bytes, actual)
    case V.Interrupted{field_prefix}: no_prepared(V.fact(c, binding, public, V.Interrupted{field_prefix}), response, bytes, actual)
    case V.Closed{}: no_prepared(V.fact(c, binding, public, V.Closed{}), response, bytes, actual)

def invalidation_prepared(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, phase: N.InvalidationEvent, +response: S.Response, +bytes: List<&2, U32>,
  actual: {M.invalidation_prepared(phase) == Some{M.Framing{response, bytes}} : Maybe<&2, M.Framing>}) ->
  {N.fact(c, binding, public, phase) == E.PreparedKernel{I.Prepared{response, bytes}} : E.Fact}:
  match phase:
    case N.InvalidationBase{base}: phase_prepared(c, binding, public, base, response, bytes, actual)
    case N.RegistryRemoved{handle, before, after}: no_prepared(E.Mutated{True{}, E.Invalidate{handle}, before, after}, response, bytes, actual)

def event_prepared(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, event: O.AuditEvent, +response: S.Response, +bytes: List<&2, U32>,
  actual: {M.prepared(event) == Some{M.Framing{response, bytes}} : Maybe<&2, M.Framing>}) ->
  {O.fact(c, binding, public, event) == E.PreparedKernel{I.Prepared{response, bytes}} : E.Fact}:
  match event:
    case O.Core{mode, code, frame}: frame_prepared(c, Source.program(binding, Host.origin(public, code)), mode, frame, response, bytes, actual)
    case O.BoundCore{mode, origin, frame}: frame_prepared(c, Source.program(binding, origin), mode, frame, response, bytes, actual)
    case O.Preparation{phase}: phase_prepared(c, binding, public, phase, response, bytes, actual)
    case O.Invalidation{phase}: invalidation_prepared(c, binding, public, phase, response, bytes, actual)
    case O.Selection{snapshot}: no_prepared(E.Selected{snapshot}, response, bytes, actual)
    case O.Resolution{+raw, +entry, context}: no_prepared(O.fact(c, binding, public, O.Resolution{raw, entry, context}), response, bytes, actual)
    case O.Publication{mode, published_response, published_bytes, before, after}: no_prepared(E.Mutated{mode, E.Publish{published_response, published_bytes}, before, after}, response, bytes, actual)
