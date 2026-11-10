# Cofact-safe metadata projection. A database publication retains its genuine
# second fact, but neither fact can impersonate a metadata receipt.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Interface.bend as I
import ../../../../contract/Logic.bend as L
import ../../../../contract/PreparedLaws.bend as H
import ../../../../contract/PreparedProtocol.bend as W
import ../../../../contract/Semantics.bend as S
import ../../../SourceService.bend as Source
import ../../../Foundations.bend as F
import ../../specification/ServiceLaws.bend as E
import ../../phases/PreparePhases.bend as V
import ../../phases/InvalidationPhases.bend as N
import ../../model/EventObserver.bend as O
import ./RuntimeSyntax.bend as Runtime

type View is Data:
  NoReceipt{}
  Metadata{receipt: W.Receipt, result: H.ControlResult, snapshot: E.Snapshot, closes: Bool}

def fact(fact: E.Fact) -> View:
  match fact:
    case E.ReceiptConcluded{receipt, result, snapshot, closes}: Metadata{receipt, result, snapshot, closes}
    case _: NoReceipt{}

def phase(phase: V.PreparationEvent) -> View:
  match phase:
    case V.ReceiptConcluded{receipt, result, snapshot, closes}: Metadata{receipt, result, snapshot, closes}
    case _: NoReceipt{}

def event(event: O.AuditEvent) -> View:
  match event:
    case O.Preparation{value}: phase(value)
    case O.Invalidation{N.InvalidationBase{value}}: phase(value)
    case _: NoReceipt{}

def phase_faithful(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, value: V.PreparationEvent) ->
  {phase(value) == fact(V.fact(c, binding, public, value)) : View}:
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

law metadata_projection_preserves_the_full_payload_of_every_actual_source_event:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +value: O.AuditEvent
  {event(value) == fact(O.fact(c, binding, public, value)) : View}
def metadata_projection_preserves_the_full_payload_of_every_actual_source_event(c, binding, public, value):
  match value:
    case O.Core{False{}, code, frame}: {==}
    case O.Core{True{}, code, frame}: {==}
    case O.BoundCore{False{}, origin, frame}: {==}
    case O.BoundCore{True{}, origin, frame}: {==}
    case O.Preparation{value}: phase_faithful(c, binding, public, value)
    case O.Invalidation{N.InvalidationBase{value}}: phase_faithful(c, binding, public, value)
    case O.Invalidation{N.RegistryRemoved{handle, before, after}}: {==}
    case O.Selection{snapshot}: {==}
    case O.Resolution{raw, entry, context}: {==}
    case O.Publication{mode, response, bytes, before, after}: {==}

def cofact_projection(+value: O.AuditEvent, -claim: E.Fact, cofact: O.PublicationFact(value, claim)) ->
  {event(value) == fact(claim) : View}:
  match value:
    case O.Core{mode, code, frame}: L.ex_false({event(O.Core{mode, code, frame}) == fact(claim) : View}, cofact)
    case O.BoundCore{mode, origin, frame}: L.ex_false({event(O.BoundCore{mode, origin, frame}) == fact(claim) : View}, cofact)
    case O.Preparation{phase}: L.ex_false({event(O.Preparation{phase}) == fact(claim) : View}, cofact)
    case O.Invalidation{phase}: L.ex_false({event(O.Invalidation{phase}) == fact(claim) : View}, cofact)
    case O.Selection{snapshot}: L.ex_false({event(O.Selection{snapshot}) == fact(claim) : View}, cofact)
    case O.Resolution{raw, entry, context}: L.ex_false({event(O.Resolution{raw, entry, context}) == fact(claim) : View}, cofact)
    case O.Publication{False{}, response, bytes, before, after}:
      Equal.cong(E.Fact, View, fact, E.Ordinary{I.Published{E.database(after)}}, claim,
        Equal.sym(E.Fact, claim, E.Ordinary{I.Published{E.database(after)}}, cofact))
    case O.Publication{True{}, response, bytes, before, after}:
      Equal.cong(E.Fact, View, fact, E.PreparedKernel{I.Published{E.database(after)}}, claim,
        Equal.sym(E.Fact, claim, E.PreparedKernel{I.Published{E.database(after)}}, cofact))

law metadata_projection_retains_both_canonical_and_publication_cofact_observations:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +value: O.AuditEvent
  for -claim: E.Fact
  for relation: O.RelFact(c, binding, public, value, claim)
  {event(value) == fact(claim) : View}
def metadata_projection_retains_both_canonical_and_publication_cofact_observations(c, binding, public, value, claim, relation):
  match relation:
    case L.Left{same}:
      Equal.trans(View, event(value), fact(O.fact(c, binding, public, value)), fact(claim),
        metadata_projection_preserves_the_full_payload_of_every_actual_source_event(c, binding, public, value),
        Equal.cong(E.Fact, View, fact, O.fact(c, binding, public, value), claim,
          Equal.sym(E.Fact, claim, O.fact(c, binding, public, value), same)))
    case L.Right{cofact}: cofact_projection(value, claim, cofact)

def runtime_absent(+value: O.AuditEvent, syntax: Runtime.Allowed(value)) -> {event(value) == NoReceipt{} : View}:
  match value:
    case O.Core{mode, code, frame}: {==}
    case O.BoundCore{mode, origin, frame}: {==}
    case O.Selection{snapshot}: {==}
    case O.Resolution{raw, entry, context}: {==}
    case O.Publication{mode, response, bytes, before, after}: {==}
    case O.Preparation{phase}: L.ex_false({event(O.Preparation{phase}) == NoReceipt{} : View}, syntax)
    case O.Invalidation{phase}: L.ex_false({event(O.Invalidation{phase}) == NoReceipt{} : View}, syntax)

def present(view: View) -> Bool:
  match view:
    case NoReceipt{}: False{}
    case Metadata{receipt, result, snapshot, closes}: True{}

law an_actual_runtime_syntax_event_cannot_impersonate_a_metadata_receipt_even_through_its_publication_cofact:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +value: O.AuditEvent
  for +receipt: W.Receipt
  for +result: H.ControlResult
  for +snapshot: E.Snapshot
  for +closes: Bool
  for syntax: Runtime.Allowed(value)
  for relation: O.RelFact(c, binding, public, value, E.ReceiptConcluded{receipt, result, snapshot, closes})
  Empty
def an_actual_runtime_syntax_event_cannot_impersonate_a_metadata_receipt_even_through_its_publication_cofact(c, binding, public, value, receipt, result, snapshot, closes, syntax, relation):
  F.false_negative_true(Equal.cong(View, Bool, present, NoReceipt{}, Metadata{receipt, result, snapshot, closes},
    Equal.trans(View, NoReceipt{}, event(value), Metadata{receipt, result, snapshot, closes},
      Equal.sym(View, event(value), NoReceipt{}, runtime_absent(value, syntax)),
      metadata_projection_retains_both_canonical_and_publication_cofact_observations(c, binding, public, value,
        E.ReceiptConcluded{receipt, result, snapshot, closes}, relation))))
