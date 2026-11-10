# DATA classification of exact sealed-entry payloads. The original full Fact
# and its affine Program remain retained through RelFact; this is not Observes.
# Other facts remain in the observer; this view never defines Observes.
import Base
import ../../../../../contract/PreparedRegistry.bend as G
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/Semantics.bend as S
import ../../../../../contract/Interface.bend as I
import ../../../../SourceService.bend as Source
import ../../../../HostTransitions.bend as Host
import ../../../../ProtocolService.bend as Q
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../phases/InvalidationPhases.bend as N
import ../../../model/EventObserver.bend as O
import ./PreparationCauses.bend as Late
import ../RuntimeSyntax.bend as Runtime
import ../ExecutionEnvelope.bend as Envelope

type View is Data:
  Void{}
  Sealed{entry: G.Entry}


def fact(value: E.Fact) -> View:
  match value:
    case E.ArtifactSealed{entry, program}: Sealed{entry}
    case _: Void{}


def phase(value: V.PreparationEvent) -> View:
  match value:
    case V.ArtifactSealed{entry}: Sealed{entry}
    case _: Void{}


def event(value: O.AuditEvent) -> View:
  match value:
    case O.Preparation{item}: phase(item)
    case O.Invalidation{N.InvalidationBase{item}}: phase(item)
    case _: Void{}


def Relevant(view: View) -> Type:
  match view:
    case Void{}: Empty
    case _: Unit


def NoSitePhase(value: V.PreparationEvent) -> Type:
  Late.Quiet(value)


def NoSite(value: O.AuditEvent) -> Type:
  match value:
    case O.Preparation{item}: NoSitePhase(item)
    case O.Invalidation{N.InvalidationBase{item}}: NoSitePhase(item)
    case _: Unit


def core_fact_view(mode: Bool, f: I.Fact) -> {fact(E.core_fact(mode, f)) == Void{} : View}:
  match mode:
    case False{}: {==}
    case True{}: {==}


def phase_interpretation(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +p: V.PreparationEvent) ->
  {fact(V.fact(c, binding, public, p)) == phase(p) : View}:
  match p:
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


def canonical_interpretation(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +item: O.AuditEvent) ->
  {fact(O.fact(c, binding, public, item)) == event(item) : View}:
  match item:
    case O.Core{mode, code, frame}: core_fact_view(mode, Q.fact_of_frame(c, Source.program(binding, Host.origin(public, code)), frame))
    case O.BoundCore{mode, origin, frame}: core_fact_view(mode, Q.fact_of_frame(c, Source.program(binding, origin), frame))
    case O.Preparation{p}: phase_interpretation(c, binding, public, p)
    case O.Invalidation{N.InvalidationBase{p}}: phase_interpretation(c, binding, public, p)
    case O.Invalidation{N.RegistryRemoved{handle, before, after}}: {==}
    case O.Selection{snapshot}: {==}
    case O.Resolution{raw, entry, context}: {==}
    case O.Publication{mode, response, bytes, before, after}: {==}


def irrelevant(-view: View, relevant: Relevant(view), absent: {view == Void{} : View}) -> Empty:
  %absent : Relevant(_) relevant


def phase_excluded(+p: V.PreparationEvent, excluded: NoSitePhase(p)) -> {phase(p) == Void{} : View}:
  match p:
    case V.WireReceived{wire}: {==}
    case V.IdentityEstablished{wire, context}: {==}
    case V.Accepted{wire, context}: {==}
    case V.Refuted{wire, context}: {==}
    case V.PrimitiveFailed{stage, identifier, fatal}: {==}
    case V.HandleChosen{handle}: {==}
    case V.ReceiptPrepared{receipt, bytes}: {==}
    case V.ArtifactSealed{entry}: L.ex_false({Sealed{entry} == Void{} : View}, excluded)
    case V.RegistryChanged{entry, before, after}: {==}
    case V.ReceiptConcluded{receipt, result, snapshot, closes}: {==}
    case V.ErrorPrepared{status, bytes}: {==}
    case V.ErrorConcluded{status, snapshot, closes}: {==}
    case V.Delivered{bytes}: {==}
    case V.Interrupted{prefix}: {==}
    case V.Closed{}: {==}


def excluded(+e: O.AuditEvent, absent: NoSite(e)) -> {event(e) == Void{} : View}:
  match e:
    case O.Core{mode, code, frame}: {==}
    case O.BoundCore{mode, origin, frame}: {==}
    case O.Preparation{p}: phase_excluded(p, absent)
    case O.Invalidation{N.InvalidationBase{p}}: phase_excluded(p, absent)
    case O.Invalidation{N.RegistryRemoved{handle, before, after}}: {==}
    case O.Selection{snapshot}: {==}
    case O.Resolution{raw, entry, context}: {==}
    case O.Publication{mode, response, bytes, before, after}: {==}



def runtime_absent(+value: O.AuditEvent, syntax: Runtime.Allowed(value)) -> {event(value) == Void{} : View}:
  match value:
    case O.Core{mode, code, frame}: {==}
    case O.BoundCore{mode, origin, frame}: {==}
    case O.Selection{snapshot}: {==}
    case O.Resolution{raw, entry, context}: {==}
    case O.Publication{mode, response, bytes, before, after}: {==}
    case O.Preparation{phase}: L.ex_false({event(O.Preparation{phase}) == Void{} : View}, syntax)
    case O.Invalidation{phase}: L.ex_false({event(O.Invalidation{phase}) == Void{} : View}, syntax)


def envelope_phase_absent(+p: V.PreparationEvent, allowed: Envelope.Allowed(O.Preparation{p})) -> {phase(p) == Void{} : View}:
  match p:
    case V.Accepted{wire, context}: {==}
    case V.HandleChosen{handle}: {==}
    case V.WireReceived{wire}: {==}
    case V.IdentityEstablished{wire, context}: {==}
    case V.Refuted{wire, context}: {==}
    case V.PrimitiveFailed{stage, identifier, fatal}: {==}
    case V.ReceiptPrepared{receipt, bytes}: {==}
    case V.ArtifactSealed{entry}: L.ex_false({Sealed{entry} == Void{} : View}, allowed)
    case V.RegistryChanged{entry, before, after}: {==}
    case V.ReceiptConcluded{receipt, result, snapshot, closes}: {==}
    case V.ErrorPrepared{status, bytes}: {==}
    case V.ErrorConcluded{status, snapshot, closes}: {==}
    case V.Delivered{bytes}: {==}
    case V.Interrupted{prefix}: {==}
    case V.Closed{}: {==}


def envelope_absent(+value: O.AuditEvent, allowed: Envelope.Allowed(value)) -> {event(value) == Void{} : View}:
  match value:
    case O.Core{mode, code, frame}: {==}
    case O.BoundCore{mode, origin, frame}: {==}
    case O.Selection{snapshot}: {==}
    case O.Resolution{raw, entry, context}: {==}
    case O.Publication{mode, response, bytes, before, after}: {==}
    case O.Preparation{phase}: envelope_phase_absent(phase, allowed)
    case O.Invalidation{phase}: L.ex_false({event(O.Invalidation{phase}) == Void{} : View}, allowed)
