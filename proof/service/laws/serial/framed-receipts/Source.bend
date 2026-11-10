# Complete actual Dispatch fold. Only real preparation/invalidation phases
# create metadata frames; runtime and cached headers cannot impersonate them.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Resources.bend as X
import ../../../../../contract/Semantics.bend as S
import ../../../../SourceService.bend as Source
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../phases/InvalidationPhases.bend as N
import ../../../model/EventObserver.bend as O
import ../../../model/serial/Common.bend as C
import ../../../model/serial/Decode.bend as Decode
import ../../../model/serial/Dispatch.bend as Dispatch
import ../RuntimeSyntax.bend as Runtime
import ../RuntimeSourceBase.bend as RuntimeBase
import ../ExecutionEnvelope.bend as Envelope
import ./Phases.bend as Preparation
import ./Invalidation.bend as Invalidation

def Claim(~c: S.Configuration, event: O.AuditEvent) -> Type:
  match event:
    case O.Preparation{phase}: Preparation.Claim(c, phase)
    case O.Invalidation{phase}: Invalidation.Claim(c, phase)
    case _: Unit

def All(~c: S.Configuration, events: List<&2, O.AuditEvent>) -> Type:
  match events:
    case Nil{}: Unit
    case Con{event, rest}: L.E<Claim(c, event), All(c, rest)>

def envelope_phase(~c: S.Configuration, phase: V.PreparationEvent, allowed: Envelope.Allowed(O.Preparation{phase})) -> Preparation.Claim(c, phase):
  match phase:
    case V.ReceiptPrepared{receipt, bytes}: L.ex_false(Preparation.Receipt(c, receipt, bytes), allowed)
    case V.WireReceived{wire}: Unit{}
    case V.IdentityEstablished{wire, context}: Unit{}
    case V.Accepted{wire, context}: Unit{}
    case V.Refuted{wire, context}: Unit{}
    case V.PrimitiveFailed{stage, identifier, fatal}: Unit{}
    case V.HandleChosen{handle}: Unit{}
    case V.ArtifactSealed{entry}: Unit{}
    case V.RegistryChanged{entry, before, after}: Unit{}
    case V.ReceiptConcluded{receipt, result, snapshot, closes}: Unit{}
    case V.ErrorPrepared{status, bytes}: Unit{}
    case V.ErrorConcluded{status, snapshot, closes}: Unit{}
    case V.Delivered{bytes}: Unit{}
    case V.Interrupted{prefix}: Unit{}
    case V.Closed{}: Unit{}

def envelope_event(~c: S.Configuration, event: O.AuditEvent, allowed: Envelope.Allowed(event)) -> Claim(c, event):
  match event:
    case O.Core{mode, code, frame}: Unit{}
    case O.BoundCore{mode, origin, frame}: Unit{}
    case O.Selection{snapshot}: Unit{}
    case O.Resolution{raw, entry, context}: Unit{}
    case O.Publication{mode, response, bytes, before, after}: Unit{}
    case O.Preparation{phase}: envelope_phase(c, phase, allowed)
    case O.Invalidation{phase}: L.ex_false(Invalidation.Claim(c, phase), allowed)

def envelope(~c: S.Configuration, events: List<&2, O.AuditEvent>, syntax: Envelope.All(events)) -> All(c, events):
  match events syntax:
    case Nil{} unit: Unit{}
    case Con{event, rest} L.Both{first, later}: L.Both{envelope_event(c, event, first), envelope(c, rest, later)}

def runtime(~c: S.Configuration, +events: List<&2, O.AuditEvent>, syntax: Runtime.All(events)) -> All(c, events):
  envelope(c, events, Envelope.runtime_events(events, syntax))

def appended(~c: S.Configuration, +prefix: List<&2, O.AuditEvent>, -tail: List<&2, O.AuditEvent>, first: All(c, prefix), later: All(c, tail)) -> All(c, C.append(prefix, tail)):
  match prefix first:
    case Nil{} unit: later
    case Con{head, +rest} L.Both{one, remaining}: L.Both{one, appended(c, rest, tail, remaining, later)}

def prefixed(~c: S.Configuration, +prefix: List<&2, O.AuditEvent>, run: C.CallRun, first: All(c, prefix), later: All(c, C.events(run))) -> All(c, C.events(C.prefix(prefix, run))):
  match run:
    case C.CallRun{events, snapshot, outcome, waiting, closed}: appended(c, prefix, events, first, later)

def preparation_events(~c: S.Configuration, phases: List<&2, V.PreparationEvent>, properties: Preparation.All(c, phases)) -> All(c, C.prepare_events(phases)):
  match phases properties:
    case Nil{} unit: Unit{}
    case Con{phase, rest} L.Both{first, later}: L.Both{first, preparation_events(c, rest, later)}

def preparation_run(~c: S.Configuration, run: V.PreparationRun, properties: Preparation.All(c, V.events(run))) -> All(c, C.events(C.preparation(run))):
  match run:
    case V.PreparationRun{events, result, snapshot, waiting, closed}: preparation_events(c, events, properties)

def preparation(~c: S.Configuration, +mode: V.Mode, +raw: P.Request, +before: E.Snapshot, +returns: V.Returns) -> All(c, C.events(C.preparation(V.run(c, mode, raw, before, returns)))):
  preparation_run(c, V.run(c, mode, raw, before, returns), Preparation.every_actual_preparation_receipt_frame_has_its_literal_encoding_and_bound_even_without_later_success(c, mode, raw, before, returns))

def invalidation_events(~c: S.Configuration, phases: List<&2, N.InvalidationEvent>, properties: Invalidation.All(c, phases)) -> All(c, C.invalidate_events(phases)):
  match phases properties:
    case Nil{} unit: Unit{}
    case Con{phase, rest} L.Both{first, later}: L.Both{first, invalidation_events(c, rest, later)}

def invalidation_run(~c: S.Configuration, run: N.InvalidationRun, properties: Invalidation.All(c, N.events(run))) -> All(c, C.events(C.invalidation(run))):
  match run:
    case N.InvalidationRun{events, result, snapshot, waiting, closed}: invalidation_events(c, events, properties)

def cleanup(primitives: Dispatch.Primitives) -> N.CleanupReturn:
  Dispatch.Primitives{check, allocation, seal, cleanup, artifact, execution, send} = primitives
  cleanup

def invalidation(~c: S.Configuration, +before: E.Snapshot, +raw: P.Request, +primitives: Dispatch.Primitives) -> All(c, C.events(C.invalidation(N.run(c, before, raw, cleanup(primitives), Dispatch.send(primitives))))):
  invalidation_run(c, N.run(c, before, raw, cleanup(primitives), Dispatch.send(primitives)),
    Invalidation.every_actual_invalidation_receipt_frame_is_encoded_and_bounded_before_any_cleanup_return(c, before, raw, cleanup(primitives), Dispatch.send(primitives)))

def extension(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +before: E.Snapshot, operation: W.Operation, +raw: P.Request, primitives: Dispatch.Primitives) -> All(c, C.events(Dispatch.extension(c, binding, public, operation, before, raw, primitives))):
  match operation primitives:
    case W.Prepare{} Dispatch.Primitives{checker, allocation, seal, cleanup, artifact, execution, send}: preparation(c, V.PrepareMode{}, raw, before, V.Returns{checker, allocation, seal, send})
    case W.PrepareRead{} Dispatch.Primitives{checker, allocation, seal, cleanup, artifact, execution, send}: preparation(c, V.ReadMode{}, raw, before, V.Returns{checker, allocation, seal, send})
    case W.Invalidate{} Dispatch.Primitives{+checker, +allocation, +seal, +clean, +artifact, +execution, +send}: invalidation(c, before, raw, Dispatch.Primitives{checker, allocation, seal, clean, artifact, execution, send})
    case W.Execute{} Dispatch.Primitives{+checker, +allocation, +seal, +clean, +artifact, +execution, +send}:
      envelope(c, C.events(Dispatch.cached(c, binding, public, before, raw, artifact, execution, send)),
        Envelope.actual_cached_execution_envelopes_have_only_their_two_real_control_headers_and_runtime_events(c, binding, public, before, raw, artifact, execution, send))

def parsed(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +before: E.Snapshot, wire: W.WireRequest, +primitives: Dispatch.Primitives) -> All(c, C.events(Dispatch.parsed(c, binding, public, before, wire, primitives))):
  match wire:
    case W.Ordinary{+raw}: envelope(c, C.events(Dispatch.ordinary(c, binding, public, before, raw, primitives)), Envelope.actual_ordinary_execution_envelopes_cannot_inject_control_phase_events(c, binding, public, before, raw, primitives))
    case W.Extension{operation, raw}: extension(c, binding, public, before, operation, raw, primitives)

def decided(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +before: E.Snapshot, decision: Decode.Decision, +primitives: Dispatch.Primitives) -> All(c, C.events(Dispatch.decoded_decision(c, binding, public, decision, before, primitives))):
  match decision:
    case Decode.Shutdown{}: L.Both{Unit{}, Unit{}}
    case Decode.TransportStopped{}: Unit{}
    case Decode.Reject{+mode, +status, +closes}: runtime(c, C.events(C.error(mode, "", before, status, closes, Dispatch.send(primitives))), RuntimeBase.error(mode, "", before, status, closes, Dispatch.send(primitives)))
    case Decode.Parsed{wire}: parsed(c, binding, public, before, wire, primitives)

def decoded(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +before: E.Snapshot, decoded: Decode.DecodeRun, +primitives: Dispatch.Primitives) -> All(c, C.events(Dispatch.decoded(c, binding, public, before, decoded, primitives))):
  match decoded:
    case Decode.DecodeRun{+decision, +frames}:
      prefixed(c, C.core(Dispatch.decision_mode(decision), Dispatch.decision_code(decision), frames), Dispatch.decoded_decision(c, binding, public, decision, before, primitives),
        runtime(c, C.core(Dispatch.decision_mode(decision), Dispatch.decision_code(decision), frames), RuntimeBase.core(Dispatch.decision_mode(decision), Dispatch.decision_code(decision), frames)),
        decided(c, binding, public, before, decision, primitives))

law every_actual_complete_dispatch_retains_encoding_and_limits_of_every_metadata_prepared_frame:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +before: E.Snapshot
  for +input: X.Reception
  for +primitives: Dispatch.Primitives
  All(c, C.events(Dispatch.run(c, binding, public, before, input, primitives)))
def every_actual_complete_dispatch_retains_encoding_and_limits_of_every_metadata_prepared_frame(c, binding, public, before, input, primitives):
  decoded(c, binding, public, before, Decode.run(c, E.database(before), input), primitives)
