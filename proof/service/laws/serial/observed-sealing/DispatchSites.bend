# Every actual dispatch metadata event has an original reached preparation or
# invalidation cause. No desired result/trace/Current/validity is an input.
import Base
import ../../../../../contract/PreparedRegistry.bend as G
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Semantics.bend as S
import ../../../../../contract/Resources.bend as X
import ../../../../SourceService.bend as Source
import ../../../../Foundations.bend as F
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../phases/InvalidationPhases.bend as N
import ../../../model/EventObserver.bend as O
import ../../../model/FrameBounds.bend as B
import ../../../model/serial/Common.bend as C
import ../../../model/serial/Decode.bend as Decode
import ../../../model/serial/Dispatch.bend as Dispatch
import ../../../model/serial/PreparationPrelude.bend as Prelude
import ./PreparationCauses.bend as Preparation
import ./InvalidationAbsent.bend as Invalidation
import ./Absent.bend as Absent
import ../RuntimeSyntax.bend as Runtime
import ../RuntimeSourceBase.bend as RuntimeBase
import ../ExecutionEnvelope.bend as Envelope
import ./SealingData.bend as Projection

def cleanup(primitives: Dispatch.Primitives) -> N.CleanupReturn:
  Dispatch.Primitives{checker, allocator, seal, cleanup, artifact, execution, send} = primitives
  cleanup

type Cause<-c: S.Configuration, -before: E.Snapshot, -decision: Decode.Decision, -primitives: Dispatch.Primitives,
  -entry: G.Entry> is Data:
  PreparationCause{mode: V.Mode, raw: P.Request,
    parsed: {decision == Decode.Parsed{W.Extension{V.operation(mode), raw}} : Decode.Decision},
    cause: Preparation.Cause<c, mode, raw, before, Prelude.returns(primitives), V.ArtifactSealed{entry}>}

def ViewClaim(-c: S.Configuration, -before: E.Snapshot, -decision: Decode.Decision, -primitives: Dispatch.Primitives, view: Projection.View) -> Type:
  match view:
    case Projection.Void{}: Unit
    case Projection.Sealed{entry}: Cause<c, before, decision, primitives, entry>

def Claim(-c: S.Configuration, -before: E.Snapshot, -decision: Decode.Decision, -primitives: Dispatch.Primitives, event: O.AuditEvent) -> Type:
  ViewClaim(c, before, decision, primitives, Projection.event(event))

def All(-c: S.Configuration, -before: E.Snapshot, -decision: Decode.Decision, -primitives: Dispatch.Primitives, events: List<&2, O.AuditEvent>) -> Type:
  match events:
    case Nil{}: Unit
    case Con{event, rest}: L.E<Claim(c, before, decision, primitives, event), All(c, before, decision, primitives, rest)>

def quiet(-c: S.Configuration, -before: E.Snapshot, -decision: Decode.Decision, -primitives: Dispatch.Primitives, +event: O.AuditEvent,
  absent: {Projection.event(event) == Projection.Void{} : Projection.View}) -> Claim(c, before, decision, primitives, event):
  %Equal.sym(Projection.View, Projection.event(event), Projection.Void{}, absent) : ViewClaim(c, before, decision, primitives, _)
  Unit{}

def runtime(-c: S.Configuration, -before: E.Snapshot, -decision: Decode.Decision, -primitives: Dispatch.Primitives,
  events: List<&2, O.AuditEvent>, syntax: Runtime.All(events)) -> All(c, before, decision, primitives, events):
  match events syntax:
    case Nil{} unit: Unit{}
    case Con{+event, rest} L.Both{head, later}:
      L.Both{quiet(c, before, decision, primitives, event, Projection.runtime_absent(event, head)), runtime(c, before, decision, primitives, rest, later)}

def envelope(-c: S.Configuration, -before: E.Snapshot, -decision: Decode.Decision, -primitives: Dispatch.Primitives,
  events: List<&2, O.AuditEvent>, syntax: Envelope.All(events)) -> All(c, before, decision, primitives, events):
  match events syntax:
    case Nil{} unit: Unit{}
    case Con{+event, rest} L.Both{head, later}:
      L.Both{quiet(c, before, decision, primitives, event, Projection.envelope_absent(event, head)), envelope(c, before, decision, primitives, rest, later)}

def appended(-c: S.Configuration, -before: E.Snapshot, -decision: Decode.Decision, -primitives: Dispatch.Primitives,
  +prefix: List<&2, O.AuditEvent>, -tail: List<&2, O.AuditEvent>, first: All(c, before, decision, primitives, prefix), later: All(c, before, decision, primitives, tail)) ->
  All(c, before, decision, primitives, C.append(prefix, tail)):
  match prefix first:
    case Nil{} unit: later
    case Con{event, +rest} L.Both{head, remaining}: L.Both{head, appended(c, before, decision, primitives, rest, tail, remaining, later)}

def prefixed(-c: S.Configuration, -before: E.Snapshot, -decision: Decode.Decision, -primitives: Dispatch.Primitives,
  +prefix: List<&2, O.AuditEvent>, run: C.CallRun, first: All(c, before, decision, primitives, prefix), later: All(c, before, decision, primitives, C.events(run))) ->
  All(c, before, decision, primitives, C.events(C.prefix(prefix, run))):
  match run:
    case C.CallRun{events, snapshot, outcome, waiting, closed}: appended(c, before, decision, primitives, prefix, events, first, later)

# The only information consumed here is DATA reconstructed by the actual phase
# theorem. Nonreceipt phases cannot fabricate an extra metadata event.
def preparation_event(~c: S.Configuration, +before: E.Snapshot, +mode: V.Mode, +raw: P.Request, +primitives: Dispatch.Primitives,
  phase: V.PreparationEvent, cause: Preparation.Claim(c, mode, raw, before, Prelude.returns(primitives), phase)) ->
  Claim(c, before, Decode.Parsed{W.Extension{V.operation(mode), raw}}, primitives, O.Preparation{phase}):
  match phase:
    case V.ArtifactSealed{entry}: PreparationCause{mode, raw, {==}, cause}
    case V.ReceiptConcluded{receipt, result, snapshot, closes}: Unit{}
    case V.WireReceived{wire}: Unit{}
    case V.IdentityEstablished{wire, context}: Unit{}
    case V.Accepted{wire, context}: Unit{}
    case V.Refuted{wire, context}: Unit{}
    case V.PrimitiveFailed{stage, identifier, fatal}: Unit{}
    case V.HandleChosen{handle}: Unit{}
    case V.ReceiptPrepared{receipt, bytes}: Unit{}
    case V.RegistryChanged{entry, before, after}: Unit{}
    case V.ErrorPrepared{status, bytes}: Unit{}
    case V.ErrorConcluded{status, snapshot, closes}: Unit{}
    case V.Delivered{bytes}: Unit{}
    case V.Interrupted{prefix}: Unit{}
    case V.Closed{}: Unit{}

def preparation_events(~c: S.Configuration, +before: E.Snapshot, +mode: V.Mode, +raw: P.Request, +primitives: Dispatch.Primitives,
  phases: List<&2, V.PreparationEvent>, causes: Preparation.All(c, mode, raw, before, Prelude.returns(primitives), phases)) ->
  All(c, before, Decode.Parsed{W.Extension{V.operation(mode), raw}}, primitives, C.prepare_events(phases)):
  match phases causes:
    case Nil{} unit: Unit{}
    case Con{phase, rest} L.Both{head, later}:
      L.Both{preparation_event(c, before, mode, raw, primitives, phase, head), preparation_events(c, before, mode, raw, primitives, rest, later)}

def preparation_run(~c: S.Configuration, +before: E.Snapshot, +mode: V.Mode, +raw: P.Request, +primitives: Dispatch.Primitives,
  run: V.PreparationRun, causes: Preparation.All(c, mode, raw, before, Prelude.returns(primitives), V.events(run))) ->
  All(c, before, Decode.Parsed{W.Extension{V.operation(mode), raw}}, primitives, C.events(C.preparation(run))):
  match run:
    case V.PreparationRun{events, result, snapshot, waiting, closed}: preparation_events(c, before, mode, raw, primitives, events, causes)

def prepare(~c: S.Configuration, +before: E.Snapshot, +mode: V.Mode, +raw: P.Request, +primitives: Dispatch.Primitives) ->
  All(c, before, Decode.Parsed{W.Extension{V.operation(mode), raw}}, primitives,
    C.events(C.preparation(V.run(c, mode, raw, before, Prelude.returns(primitives))))):
  preparation_run(c, before, mode, raw, primitives, V.run(c, mode, raw, before, Prelude.returns(primitives)),
    Preparation.every_actual_sealing_event_recovers_its_original_reached_authentication_check_allocation_framing_and_seal_returns(c, mode, raw, before, Prelude.returns(primitives)))

def invalidation_events(-c: S.Configuration, -before: E.Snapshot, -decision: Decode.Decision, -primitives: Dispatch.Primitives,
  events: List<&2, O.AuditEvent>, no_seal: Absent.All(events)) -> All(c, before, decision, primitives, events):
  match events no_seal:
    case Nil{} unit: Unit{}
    case Con{+event, rest} L.Both{head, later}:
      L.Both{quiet(c, before, decision, primitives, event, Projection.excluded(event, head)), invalidation_events(c, before, decision, primitives, rest, later)}


def invalidate(~c: S.Configuration, +before: E.Snapshot, +raw: P.Request, +primitives: Dispatch.Primitives) ->
  All(c, before, Decode.Parsed{W.Extension{W.Invalidate{}, raw}}, primitives,
    C.events(C.invalidation(N.run(c, before, raw, cleanup(primitives), Dispatch.send(primitives))))):
  invalidation_events(c, before, Decode.Parsed{W.Extension{W.Invalidate{}, raw}}, primitives,
    C.events(C.invalidation(N.run(c, before, raw, cleanup(primitives), Dispatch.send(primitives)))),
    Invalidation.call(N.run(c, before, raw, cleanup(primitives), Dispatch.send(primitives)), Invalidation.run(c, before, raw, cleanup(primitives), Dispatch.send(primitives))))


def extension(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +before: E.Snapshot, +operation: W.Operation, +raw: P.Request, +primitives: Dispatch.Primitives) ->
  All(c, before, Decode.Parsed{W.Extension{operation, raw}}, primitives, C.events(Dispatch.extension(c, binding, public, operation, before, raw, primitives))):
  match operation primitives:
    case W.Prepare{} Dispatch.Primitives{+checker, +allocator, +seal, +clean, +artifact, +execution, +send}:
      prepare(c, before, V.PrepareMode{}, raw, Dispatch.Primitives{checker, allocator, seal, clean, artifact, execution, send})
    case W.PrepareRead{} Dispatch.Primitives{+checker, +allocator, +seal, +clean, +artifact, +execution, +send}:
      prepare(c, before, V.ReadMode{}, raw, Dispatch.Primitives{checker, allocator, seal, clean, artifact, execution, send})
    case W.Invalidate{} Dispatch.Primitives{+checker, +allocator, +seal, +clean, +artifact, +execution, +send}:
      invalidate(c, before, raw, Dispatch.Primitives{checker, allocator, seal, clean, artifact, execution, send})
    case W.Execute{} Dispatch.Primitives{+checker, +allocator, +seal, +clean, +artifact, +execution, +send}:
      envelope(c, before, Decode.Parsed{W.Extension{W.Execute{}, raw}}, Dispatch.Primitives{checker, allocator, seal, clean, artifact, execution, send},
        C.events(Dispatch.cached(c, binding, public, before, raw, artifact, execution, send)),
        Envelope.actual_cached_execution_envelopes_have_only_their_two_real_control_headers_and_runtime_events(c, binding, public, before, raw, artifact, execution, send))

def parsed(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +before: E.Snapshot, +wire: W.WireRequest, +primitives: Dispatch.Primitives) ->
  All(c, before, Decode.Parsed{wire}, primitives, C.events(Dispatch.parsed(c, binding, public, before, wire, primitives))):
  match wire:
    case W.Ordinary{+raw}:
      envelope(c, before, Decode.Parsed{W.Ordinary{raw}}, primitives, C.events(Dispatch.ordinary(c, binding, public, before, raw, primitives)),
        Envelope.actual_ordinary_execution_envelopes_cannot_inject_control_phase_events(c, binding, public, before, raw, primitives))
    case W.Extension{operation, raw}: extension(c, binding, public, before, operation, raw, primitives)

def decided(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +before: E.Snapshot, +decision: Decode.Decision, +primitives: Dispatch.Primitives) ->
  All(c, before, decision, primitives, C.events(Dispatch.decoded_decision(c, binding, public, decision, before, primitives))):
  match decision:
    case Decode.Shutdown{}: L.Both{Unit{}, Unit{}}
    case Decode.TransportStopped{}: Unit{}
    case Decode.Reject{+mode, +status, +closes}:
      runtime(c, before, Decode.Reject{mode, status, closes}, primitives,
        C.events(C.error(mode, "", before, status, closes, Dispatch.send(primitives))), RuntimeBase.error(mode, "", before, status, closes, Dispatch.send(primitives)))
    case Decode.Parsed{wire}: parsed(c, binding, public, before, wire, primitives)

def decoded(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +before: E.Snapshot, +decoded: Decode.DecodeRun, +primitives: Dispatch.Primitives) ->
  All(c, before, Decode.decision(decoded), primitives, C.events(Dispatch.decoded(c, binding, public, before, decoded, primitives))):
  match decoded:
    case Decode.DecodeRun{+decision, +frames}:
      prefixed(c, before, decision, primitives, C.core(Dispatch.decision_mode(decision), Dispatch.decision_code(decision), frames),
        Dispatch.decoded_decision(c, binding, public, decision, before, primitives),
        runtime(c, before, decision, primitives, C.core(Dispatch.decision_mode(decision), Dispatch.decision_code(decision), frames),
          RuntimeBase.core(Dispatch.decision_mode(decision), Dispatch.decision_code(decision), frames)),
        decided(c, binding, public, before, decision, primitives))

law every_actual_dispatch_seal_event_has_its_original_reached_preparation_cause:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +before: E.Snapshot
  for +input: X.Reception
  for +primitives: Dispatch.Primitives
  All(c, before, Decode.decision(Decode.run(c, E.database(before), input)), primitives, C.events(Dispatch.run(c, binding, public, before, input, primitives)))
def every_actual_dispatch_seal_event_has_its_original_reached_preparation_cause(c, binding, public, before, input, primitives):
  decoded(c, binding, public, before, Decode.run(c, E.database(before), input), primitives)

def query(~c: S.Configuration, +before: E.Snapshot, +decision: Decode.Decision, +primitives: Dispatch.Primitives,
  +events: List<&2, O.AuditEvent>, index: Nat, +event: O.AuditEvent,
  all: All(c, before, decision, primitives, events), found: {B.query(O.AuditEvent, events, index) == Some{event} : Maybe<&2, O.AuditEvent>}) ->
  Claim(c, before, decision, primitives, event):
  match events index all:
    case Nil{} _ unit: L.ex_false(Claim(c, before, decision, primitives, event), F.none_negative_some(O.AuditEvent, event, found))
    case Con{+head, rest} Zero{} L.Both{claim, later}:
      %F.some_injective(O.AuditEvent, head, event, found) : Claim(c, before, decision, primitives, _)
      claim
    case Con{head, +rest} Succ{prior} L.Both{claim, later}: query(c, before, decision, primitives, rest, prior, event, later, found)
