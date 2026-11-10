# Lossless DATA classification only for the two host header fact constructors.
# Other facts remain in the observer; this view never defines Observes.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/Semantics.bend as S
import ../../../../../contract/Interface.bend as I
import ../../../../SourceService.bend as Source
import ../../../../HostTransitions.bend as Host
import ../../../../ProtocolService.bend as Q
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../phases/InvalidationPhases.bend as N
import ../../../model/EventObserver.bend as O

type View is Data:
  Void{}
  Wire{wire: W.WireRequest}
  Identity{wire: W.WireRequest, context: Maybe<&2, D.Context>}


def fact(value: E.Fact) -> View:
  match value:
    case E.WireReceived{wire}: Wire{wire}
    case E.IdentityEstablished{wire, context}: Identity{wire, context}
    case _: Void{}


def phase(value: V.PreparationEvent) -> View:
  match value:
    case V.WireReceived{wire}: Wire{wire}
    case V.IdentityEstablished{wire, context}: Identity{wire, context}
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


def NoHeaderPhase(value: V.PreparationEvent) -> Type:
  match value:
    case V.WireReceived{wire}: Empty
    case V.IdentityEstablished{wire, context}: Empty
    case _: Unit


def NoHeader(value: O.AuditEvent) -> Type:
  match value:
    case O.Preparation{item}: NoHeaderPhase(item)
    case O.Invalidation{N.InvalidationBase{item}}: NoHeaderPhase(item)
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


def phase_excluded(+p: V.PreparationEvent, excluded: NoHeaderPhase(p)) -> {phase(p) == Void{} : View}:
  match p:
    case V.WireReceived{wire}: Empty.absurd({Wire{wire} == Void{} : View}, excluded)
    case V.IdentityEstablished{wire, context}: Empty.absurd({Identity{wire, context} == Void{} : View}, excluded)
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


def excluded(+e: O.AuditEvent, absent: NoHeader(e)) -> {event(e) == Void{} : View}:
  match e:
    case O.Core{mode, code, frame}: {==}
    case O.BoundCore{mode, origin, frame}: {==}
    case O.Preparation{p}: phase_excluded(p, absent)
    case O.Invalidation{N.InvalidationBase{p}}: phase_excluded(p, absent)
    case O.Invalidation{N.RegistryRemoved{handle, before, after}}: {==}
    case O.Selection{snapshot}: {==}
    case O.Resolution{raw, entry, context}: {==}
    case O.Publication{mode, response, bytes, before, after}: {==}


type Point is Data:
  WirePoint{}
  IdentityPoint{}


def offset(point: Point) -> Nat:
  match point:
    case WirePoint{}: 0n
    case IdentityPoint{}: 1n


def expected(point: Point, wire: W.WireRequest, context: Maybe<&2, D.Context>) -> View:
  match point:
    case WirePoint{}: Wire{wire}
    case IdentityPoint{}: Identity{wire, context}


def expected_relevant(point: Point, -wire: W.WireRequest, -context: Maybe<&2, D.Context>) -> Relevant(expected(point, wire, context)):
  match point:
    case WirePoint{}: Unit{}
    case IdentityPoint{}: Unit{}


def is_wire(view: View) -> Bool:
  match view:
    case Wire{wire}: True{}
    case _: False{}
