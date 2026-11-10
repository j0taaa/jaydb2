# Ordinary/cached request envelopes contain runtime syntax plus only the two
# actual cached wire/identity headers. They cannot fabricate metadata receipts.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Interface.bend as I
import ../../../../contract/Logic.bend as L
import ../../../../contract/PreparedLaws.bend as H
import ../../../../contract/PreparedProtocol.bend as W
import ../../../../contract/Protocol.bend as P
import ../../../../contract/Semantics.bend as S
import ../../../SourceService.bend as Source
import ../../../PreparedDispatch.bend as Cached
import ../../../HostTransitions.bend as Host
import ../../../Foundations.bend as F
import ../../specification/ServiceLaws.bend as E
import ../../phases/PreparePhases.bend as V
import ../../model/EventObserver.bend as O
import ../../model/FrameBounds.bend as B
import ../../model/serial/Common.bend as C
import ../../model/serial/Dispatch.bend as Dispatch
import ../../model/serial/ExecutionPhases.bend as Execution
import ./RuntimeSyntax.bend as Runtime
import ./ReceiptProjection.bend as Metadata
import ./RuntimeSourceDispatch.bend as SourceSyntax

def Allowed(event: O.AuditEvent) -> Type:
  match event:
    case O.Preparation{V.WireReceived{wire}}: Unit
    case O.Preparation{V.IdentityEstablished{wire, context}}: Unit
    case _: Runtime.Allowed(event)

def All(events: List<&2, O.AuditEvent>) -> Type:
  match events:
    case Nil{}: Unit
    case Con{event, rest}: L.E<Allowed(event), All(rest)>

def from_runtime(+event: O.AuditEvent, syntax: Runtime.Allowed(event)) -> Allowed(event):
  match event:
    case O.Core{mode, code, frame}: Unit{}
    case O.BoundCore{mode, origin, frame}: Unit{}
    case O.Selection{snapshot}: Unit{}
    case O.Resolution{raw, entry, context}: Unit{}
    case O.Publication{mode, response, bytes, before, after}: Unit{}
    case O.Preparation{phase}: L.ex_false(Allowed(O.Preparation{phase}), syntax)
    case O.Invalidation{phase}: L.ex_false(Allowed(O.Invalidation{phase}), syntax)

def runtime_events(events: List<&2, O.AuditEvent>, syntax: Runtime.All(events)) -> All(events):
  match events syntax:
    case Nil{} unit: Unit{}
    case Con{event, rest} L.Both{first, later}: L.Both{from_runtime(event, first), runtime_events(rest, later)}

def appended(+prefix: List<&2, O.AuditEvent>, -tail: List<&2, O.AuditEvent>, first: All(prefix), later: All(tail)) -> All(C.append(prefix, tail)):
  match prefix first:
    case Nil{} unit: later
    case Con{head, +rest} L.Both{one, remaining}: L.Both{one, appended(rest, tail, remaining, later)}

def prefixed(+prefix: List<&2, O.AuditEvent>, run: C.CallRun, first: All(prefix), later: All(C.events(run))) -> All(C.events(C.prefix(prefix, run))):
  match run:
    case C.CallRun{events, snapshot, outcome, waiting, closed}: appended(prefix, events, first, later)

law actual_ordinary_execution_envelopes_cannot_inject_control_phase_events:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +before: E.Snapshot
  for +raw: P.Request
  for +primitives: Dispatch.Primitives
  All(C.events(Dispatch.ordinary(c, binding, public, before, raw, primitives)))
def actual_ordinary_execution_envelopes_cannot_inject_control_phase_events(c, binding, public, before, raw, primitives):
  runtime_events(C.events(Dispatch.ordinary(c, binding, public, before, raw, primitives)), SourceSyntax.ordinary(c, binding, public, before, raw, primitives))

law actual_cached_execution_envelopes_have_only_their_two_real_control_headers_and_runtime_events:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +before: E.Snapshot
  for +raw: P.Request
  for +artifact: Dispatch.ArtifactReturn
  for +execution: Execution.Request
  for +send: V.SendReturn
  All(C.events(Dispatch.cached(c, binding, public, before, raw, artifact, execution, send)))
def actual_cached_execution_envelopes_have_only_their_two_real_control_headers_and_runtime_events(c, binding, public, before, raw, artifact, execution, send):
  prefixed([O.Preparation{V.WireReceived{W.Extension{W.Execute{}, raw}}},
      O.Preparation{V.IdentityEstablished{W.Extension{W.Execute{}, raw}, D.authenticate(E.database(before), I.credential(raw))}}],
    Dispatch.cached_choice(c, binding, public, Cached.choose(E.instance(before), Host.Published{E.database(before), E.last_response(before), E.registry(before)}, raw), before, raw, artifact, execution, send),
    L.Both{Unit{}, L.Both{Unit{}, Unit{}}},
    runtime_events(C.events(Dispatch.cached_choice(c, binding, public, Cached.choose(E.instance(before), Host.Published{E.database(before), E.last_response(before), E.registry(before)}, raw), before, raw, artifact, execution, send)),
      SourceSyntax.cached_choice(c, binding, public, Cached.choose(E.instance(before), Host.Published{E.database(before), E.last_response(before), E.registry(before)}, raw), before, raw, artifact, execution, send)))

def query(+events: List<&2, O.AuditEvent>, index: Nat, +event: O.AuditEvent,
  all: All(events), found: {B.query(O.AuditEvent, events, index) == Some{event} : Maybe<&2, O.AuditEvent>}) -> Allowed(event):
  match events index all:
    case Nil{} _ unit: L.ex_false(Allowed(event), F.none_negative_some(O.AuditEvent, event, found))
    case Con{+head, rest} Zero{} L.Both{first, later}:
      %F.some_injective(O.AuditEvent, head, event, found) : Allowed(_)
      first
    case Con{head, +rest} Succ{prior} L.Both{first, later}: query(rest, prior, event, later, found)


def phase_absent(+phase: V.PreparationEvent, allowed: Allowed(O.Preparation{phase})) -> {Metadata.phase(phase) == Metadata.NoReceipt{} : Metadata.View}:
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
    case V.ReceiptConcluded{receipt, result, snapshot, closes}: L.ex_false({Metadata.phase(V.ReceiptConcluded{receipt, result, snapshot, closes}) == Metadata.NoReceipt{} : Metadata.View}, allowed)
    case V.ErrorPrepared{status, bytes}: {==}
    case V.ErrorConcluded{status, snapshot, closes}: {==}
    case V.Delivered{bytes}: {==}
    case V.Interrupted{prefix}: {==}
    case V.Closed{}: {==}


def metadata_absent(+value: O.AuditEvent, allowed: Allowed(value)) -> {Metadata.event(value) == Metadata.NoReceipt{} : Metadata.View}:
  match value:
    case O.Core{mode, code, frame}: {==}
    case O.BoundCore{mode, origin, frame}: {==}
    case O.Selection{snapshot}: {==}
    case O.Resolution{raw, entry, context}: {==}
    case O.Publication{mode, response, bytes, before, after}: {==}
    case O.Preparation{phase}: phase_absent(phase, allowed)
    case O.Invalidation{phase}: L.ex_false({Metadata.event(O.Invalidation{phase}) == Metadata.NoReceipt{} : Metadata.View}, allowed)

law an_actual_ordinary_or_cached_envelope_cannot_observe_a_metadata_receipt_from_either_full_fact:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +events: List<&2, O.AuditEvent>
  for +index: Nat
  for +value: O.AuditEvent
  for +receipt: W.Receipt
  for +result: H.ControlResult
  for +snapshot: E.Snapshot
  for +closes: Bool
  for all: All(events)
  for found: {B.query(O.AuditEvent, events, index) == Some{value} : Maybe<&2, O.AuditEvent>}
  for relation: O.RelFact(c, binding, public, value, E.ReceiptConcluded{receipt, result, snapshot, closes})
  Empty
def an_actual_ordinary_or_cached_envelope_cannot_observe_a_metadata_receipt_from_either_full_fact(c, binding, public, events, index, value, receipt, result, snapshot, closes, all, found, relation):
  F.false_negative_true(Equal.cong(Metadata.View, Bool, Metadata.present, Metadata.NoReceipt{}, Metadata.Metadata{receipt, result, snapshot, closes},
    Equal.trans(Metadata.View, Metadata.NoReceipt{}, Metadata.event(value), Metadata.Metadata{receipt, result, snapshot, closes},
      Equal.sym(Metadata.View, Metadata.event(value), Metadata.NoReceipt{}, metadata_absent(value, query(events, index, value, all, found))),
      Metadata.metadata_projection_retains_both_canonical_and_publication_cofact_observations(c, binding, public, value,
        E.ReceiptConcluded{receipt, result, snapshot, closes}, relation))))
