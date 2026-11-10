# Faithful DATA view of ReceiptPrepared, preserving the original full RelFact.
# Publication cofacts are excluded only for this impossible receipt constructor.
import Base
import ../../../../../contract/Interface.bend as I
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/Semantics.bend as S
import ../../../../ProtocolService.bend as Q
import ../../../../SourceService.bend as Source
import ../../../../HostTransitions.bend as Host
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../phases/InvalidationPhases.bend as N
import ../../../model/EventObserver.bend as O
import ../RuntimeSyntax.bend as Runtime
import ../ExecutionEnvelope.bend as Envelope

type View is Data:
  NoReceipt{}
  Metadata{receipt: W.Receipt, bytes: List<&2, U32>}

def fact(value: E.Fact) -> View:
  match value:
    case E.ReceiptPrepared{receipt, bytes}: Metadata{receipt, bytes}
    case _: NoReceipt{}

def phase(value: V.PreparationEvent) -> View:
  match value:
    case V.ReceiptPrepared{receipt, bytes}: Metadata{receipt, bytes}
    case _: NoReceipt{}

def event(value: O.AuditEvent) -> View:
  match value:
    case O.Preparation{item}: phase(item)
    case O.Invalidation{N.InvalidationBase{item}}: phase(item)
    case _: NoReceipt{}

def core(mode: Bool, -value: I.Fact) -> {fact(E.core_fact(mode, value)) == NoReceipt{} : View}:
  match mode:
    case False{}: {==}
    case True{}: {==}

def phase_interpretation(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +value: V.PreparationEvent) -> {fact(V.fact(c, binding, public, value)) == phase(value) : View}:
  match value:
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

def interpretation(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +value: O.AuditEvent) -> {fact(O.fact(c, binding, public, value)) == event(value) : View}:
  match value:
    case O.Core{mode, code, frame}: core(mode, Q.fact_of_frame(c, Source.program(binding, Host.origin(public, code)), frame))
    case O.BoundCore{mode, origin, frame}: core(mode, Q.fact_of_frame(c, Source.program(binding, origin), frame))
    case O.Preparation{item}: phase_interpretation(c, binding, public, item)
    case O.Invalidation{N.InvalidationBase{item}}: phase_interpretation(c, binding, public, item)
    case O.Invalidation{N.RegistryRemoved{handle, before, after}}: {==}
    case O.Selection{snapshot}: {==}
    case O.Resolution{raw, entry, context}: {==}
    case O.Publication{mode, response, bytes, before, after}: {==}

def runtime_absent(+value: O.AuditEvent, allowed: Runtime.Allowed(value)) -> {event(value) == NoReceipt{} : View}:
  match value:
    case O.Core{mode, code, frame}: {==}
    case O.BoundCore{mode, origin, frame}: {==}
    case O.Selection{snapshot}: {==}
    case O.Resolution{raw, entry, context}: {==}
    case O.Publication{mode, response, bytes, before, after}: {==}
    case O.Preparation{phase}: L.ex_false({event(O.Preparation{phase}) == NoReceipt{} : View}, allowed)
    case O.Invalidation{phase}: L.ex_false({event(O.Invalidation{phase}) == NoReceipt{} : View}, allowed)

def envelope_phase(value: V.PreparationEvent, allowed: Envelope.Allowed(O.Preparation{value})) -> {phase(value) == NoReceipt{} : View}:
  match value:
    case V.WireReceived{wire}: {==}
    case V.IdentityEstablished{wire, context}: {==}
    case V.Accepted{wire, context}: {==}
    case V.Refuted{wire, context}: {==}
    case V.PrimitiveFailed{stage, identifier, fatal}: {==}
    case V.HandleChosen{handle}: {==}
    case V.ReceiptPrepared{receipt, bytes}: L.ex_false({phase(V.ReceiptPrepared{receipt, bytes}) == NoReceipt{} : View}, allowed)
    case V.ArtifactSealed{entry}: {==}
    case V.RegistryChanged{entry, before, after}: {==}
    case V.ReceiptConcluded{receipt, result, snapshot, closes}: {==}
    case V.ErrorPrepared{status, bytes}: {==}
    case V.ErrorConcluded{status, snapshot, closes}: {==}
    case V.Delivered{bytes}: {==}
    case V.Interrupted{prefix}: {==}
    case V.Closed{}: {==}

def envelope_absent(+value: O.AuditEvent, allowed: Envelope.Allowed(value)) -> {event(value) == NoReceipt{} : View}:
  match value:
    case O.Core{mode, code, frame}: {==}
    case O.BoundCore{mode, origin, frame}: {==}
    case O.Selection{snapshot}: {==}
    case O.Resolution{raw, entry, context}: {==}
    case O.Publication{mode, response, bytes, before, after}: {==}
    case O.Preparation{phase}: envelope_phase(phase, allowed)
    case O.Invalidation{phase}: L.ex_false({event(O.Invalidation{phase}) == NoReceipt{} : View}, allowed)

def Void(view: View) -> Type:
  match view:
    case NoReceipt{}: Unit
    case Metadata{receipt, bytes}: Empty

def cofact(+value: O.AuditEvent, +receipt: W.Receipt, +bytes: List<&2, U32>, impossible: O.PublicationFact(value, E.ReceiptPrepared{receipt, bytes})) -> Empty:
  match value:
    case O.Core{mode, code, frame}: impossible
    case O.BoundCore{mode, origin, frame}: impossible
    case O.Selection{snapshot}: impossible
    case O.Resolution{raw, entry, context}: impossible
    case O.Preparation{phase}: impossible
    case O.Invalidation{phase}: impossible
    case O.Publication{+mode, response, sent, before, +after}:
      %Equal.sym(View, Metadata{receipt, bytes}, NoReceipt{}, Equal.trans(View, Metadata{receipt, bytes}, fact(E.core_fact(mode, I.Published{E.database(after)})), NoReceipt{},
        Equal.cong(E.Fact, View, fact, E.ReceiptPrepared{receipt, bytes}, E.core_fact(mode, I.Published{E.database(after)}), impossible), core(mode, I.Published{E.database(after)}))) : Void(_)
      Unit{}

def actual_event_view(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +value: O.AuditEvent, +receipt: W.Receipt, +bytes: List<&2, U32>,
  related: O.RelFact(c, binding, public, value, E.ReceiptPrepared{receipt, bytes})) -> {event(value) == Metadata{receipt, bytes} : View}:
  match related:
    case L.Left{canonical}:
      Equal.trans(View, event(value), fact(O.fact(c, binding, public, value)), Metadata{receipt, bytes}, Equal.sym(View, fact(O.fact(c, binding, public, value)), event(value), interpretation(c, binding, public, value)),
        Equal.cong(E.Fact, View, fact, O.fact(c, binding, public, value), E.ReceiptPrepared{receipt, bytes}, Equal.sym(E.Fact, E.ReceiptPrepared{receipt, bytes}, O.fact(c, binding, public, value), canonical)))
    case L.Right{impossible}: L.ex_false({event(value) == Metadata{receipt, bytes} : View}, cofact(value, receipt, bytes, impossible))
