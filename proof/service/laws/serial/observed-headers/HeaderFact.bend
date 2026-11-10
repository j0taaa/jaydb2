# Recover the exact full host header fact from its non-Void DATA view. This
# is an equality lemma; it does not add any observation or observer event.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/Semantics.bend as S
import ../../../../Foundations.bend as F
import ../../../../SourceService.bend as Source
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../phases/InvalidationPhases.bend as N
import ../../../model/EventObserver.bend as O
import ./HeaderData.bend as H


type Payload is Data:
  WirePayload{wire: W.WireRequest}
  IdentityPayload{wire: W.WireRequest, context: Maybe<&2, D.Context>}


def reify(value: Payload) -> E.Fact:
  match value:
    case WirePayload{wire}: E.WireReceived{wire}
    case IdentityPayload{wire, context}: E.IdentityEstablished{wire, context}


def payload(view: H.View) -> Maybe<&2, Payload>:
  match view:
    case H.Void{}: None{}
    case H.Wire{wire}: Some{WirePayload{wire}}
    case H.Identity{wire, context}: Some{IdentityPayload{wire, context}}


def expected_payload(point: H.Point, wire: W.WireRequest, context: Maybe<&2, D.Context>) -> Payload:
  match point:
    case H.WirePoint{}: WirePayload{wire}
    case H.IdentityPoint{}: IdentityPayload{wire, context}


def expected(point: H.Point, wire: W.WireRequest, context: Maybe<&2, D.Context>) -> E.Fact:
  reify(expected_payload(point, wire, context))


def payload_expected(point: H.Point, +wire: W.WireRequest, +context: Maybe<&2, D.Context>) ->
  {payload(H.expected(point, wire, context)) == Some{expected_payload(point, wire, context)} : Maybe<&2, Payload>}:
  match point:
    case H.WirePoint{}: {==}
    case H.IdentityPoint{}: {==}


def full_equal(+left: H.Point, +left_wire: W.WireRequest, +left_context: Maybe<&2, D.Context>,
  +right: H.Point, +right_wire: W.WireRequest, +right_context: Maybe<&2, D.Context>,
  same: {H.expected(left, left_wire, left_context) == H.expected(right, right_wire, right_context) : H.View}) ->
  {expected(left, left_wire, left_context) == expected(right, right_wire, right_context) : E.Fact}:
  Equal.cong(Payload, E.Fact, reify, expected_payload(left, left_wire, left_context), expected_payload(right, right_wire, right_context),
    F.some_injective(Payload, expected_payload(left, left_wire, left_context), expected_payload(right, right_wire, right_context),
      Equal.trans(Maybe<&2, Payload>, Some{expected_payload(left, left_wire, left_context)}, payload(H.expected(left, left_wire, left_context)), Some{expected_payload(right, right_wire, right_context)},
        Equal.sym(Maybe<&2, Payload>, payload(H.expected(left, left_wire, left_context)), Some{expected_payload(left, left_wire, left_context)}, payload_expected(left, left_wire, left_context)),
        Equal.trans(Maybe<&2, Payload>, payload(H.expected(left, left_wire, left_context)), payload(H.expected(right, right_wire, right_context)), Some{expected_payload(right, right_wire, right_context)},
          Equal.cong(H.View, Maybe<&2, Payload>, payload, H.expected(left, left_wire, left_context), H.expected(right, right_wire, right_context), same), payload_expected(right, right_wire, right_context)))))


def is_void(view: H.View) -> Bool:
  match view:
    case H.Void{}: True{}
    case _: False{}


def nonvoid(point: H.Point, +wire: W.WireRequest, +context: Maybe<&2, D.Context>, same: {H.Void{} == H.expected(point, wire, context) : H.View}) -> Empty:
  match point:
    case H.WirePoint{}: F.false_negative_true(Equal.sym(Bool, True{}, False{}, Equal.cong(H.View, Bool, is_void, H.Void{}, H.Wire{wire}, same)))
    case H.IdentityPoint{}: F.false_negative_true(Equal.sym(Bool, True{}, False{}, Equal.cong(H.View, Bool, is_void, H.Void{}, H.Identity{wire, context}, same)))


def absurd_phase(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +phase: V.PreparationEvent,
  +point: H.Point, +wire: W.WireRequest, +context: Maybe<&2, D.Context>, same: {H.Void{} == H.expected(point, wire, context) : H.View}) ->
  {V.fact(c, binding, public, phase) == expected(point, wire, context) : E.Fact}:
  L.ex_false({V.fact(c, binding, public, phase) == expected(point, wire, context) : E.Fact}, nonvoid(point, wire, context, same))


def phase(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +p: V.PreparationEvent,
  +point: H.Point, +wire: W.WireRequest, +context: Maybe<&2, D.Context>, same: {H.phase(p) == H.expected(point, wire, context) : H.View}) ->
  {V.fact(c, binding, public, p) == expected(point, wire, context) : E.Fact}:
  match p:
    case V.WireReceived{+actual}:
      full_equal(H.WirePoint{}, actual, None{}, point, wire, context, same)
    case V.IdentityEstablished{+actual, +identity}:
      full_equal(H.IdentityPoint{}, actual, identity, point, wire, context, same)
    case V.Accepted{raw, identity}: absurd_phase(c, binding, public, V.Accepted{raw, identity}, point, wire, context, same)
    case V.Refuted{raw, identity}: absurd_phase(c, binding, public, V.Refuted{raw, identity}, point, wire, context, same)
    case V.PrimitiveFailed{stage, identifier, fatal}: absurd_phase(c, binding, public, V.PrimitiveFailed{stage, identifier, fatal}, point, wire, context, same)
    case V.HandleChosen{handle}: absurd_phase(c, binding, public, V.HandleChosen{handle}, point, wire, context, same)
    case V.ReceiptPrepared{receipt, bytes}: absurd_phase(c, binding, public, V.ReceiptPrepared{receipt, bytes}, point, wire, context, same)
    case V.ArtifactSealed{entry}: absurd_phase(c, binding, public, V.ArtifactSealed{entry}, point, wire, context, same)
    case V.RegistryChanged{entry, before, after}: absurd_phase(c, binding, public, V.RegistryChanged{entry, before, after}, point, wire, context, same)
    case V.ReceiptConcluded{receipt, result, snapshot, closes}: absurd_phase(c, binding, public, V.ReceiptConcluded{receipt, result, snapshot, closes}, point, wire, context, same)
    case V.ErrorPrepared{status, bytes}: absurd_phase(c, binding, public, V.ErrorPrepared{status, bytes}, point, wire, context, same)
    case V.ErrorConcluded{status, snapshot, closes}: absurd_phase(c, binding, public, V.ErrorConcluded{status, snapshot, closes}, point, wire, context, same)
    case V.Delivered{bytes}: absurd_phase(c, binding, public, V.Delivered{bytes}, point, wire, context, same)
    case V.Interrupted{prefix}: absurd_phase(c, binding, public, V.Interrupted{prefix}, point, wire, context, same)
    case V.Closed{}: absurd_phase(c, binding, public, V.Closed{}, point, wire, context, same)


def absurd_event(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +event: O.AuditEvent,
  +point: H.Point, +wire: W.WireRequest, +context: Maybe<&2, D.Context>, same: {H.Void{} == H.expected(point, wire, context) : H.View}) ->
  {O.fact(c, binding, public, event) == expected(point, wire, context) : E.Fact}:
  L.ex_false({O.fact(c, binding, public, event) == expected(point, wire, context) : E.Fact}, nonvoid(point, wire, context, same))


def event(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, +e: O.AuditEvent,
  +point: H.Point, +wire: W.WireRequest, +context: Maybe<&2, D.Context>, same: {H.event(e) == H.expected(point, wire, context) : H.View}) ->
  {O.fact(c, binding, public, e) == expected(point, wire, context) : E.Fact}:
  match e:
    case O.Preparation{p}: phase(c, binding, public, p, point, wire, context, same)
    case O.Invalidation{N.InvalidationBase{p}}: phase(c, binding, public, p, point, wire, context, same)
    case O.Core{mode, code, frame}: absurd_event(c, binding, public, O.Core{mode, code, frame}, point, wire, context, same)
    case O.BoundCore{mode, origin, frame}: absurd_event(c, binding, public, O.BoundCore{mode, origin, frame}, point, wire, context, same)
    case O.Invalidation{N.RegistryRemoved{handle, before, after}}: absurd_event(c, binding, public, O.Invalidation{N.RegistryRemoved{handle, before, after}}, point, wire, context, same)
    case O.Selection{snapshot}: absurd_event(c, binding, public, O.Selection{snapshot}, point, wire, context, same)
    case O.Resolution{raw, entry, identity}: absurd_event(c, binding, public, O.Resolution{raw, entry, identity}, point, wire, context, same)
    case O.Publication{mode, response, bytes, before, after}: absurd_event(c, binding, public, O.Publication{mode, response, bytes, before, after}, point, wire, context, same)


def wire_of(view: H.View) -> Maybe<&2, W.WireRequest>:
  match view:
    case H.Void{}: None{}
    case H.Wire{wire}: Some{wire}
    case H.Identity{wire, context}: Some{wire}


def context_of(view: H.View) -> Maybe<&2, Maybe<&2, D.Context>>:
  match view:
    case H.Identity{wire, context}: Some{context}
    case _: None{}


def same_wire(point: H.Point, +left: W.WireRequest, +left_context: Maybe<&2, D.Context>, +right: W.WireRequest, +right_context: Maybe<&2, D.Context>,
  same: {H.expected(point, left, left_context) == H.expected(point, right, right_context) : H.View}) -> {left == right : W.WireRequest}:
  match point:
    case H.WirePoint{}: F.some_injective(W.WireRequest, left, right, Equal.cong(H.View, Maybe<&2, W.WireRequest>, wire_of, H.Wire{left}, H.Wire{right}, same))
    case H.IdentityPoint{}: F.some_injective(W.WireRequest, left, right, Equal.cong(H.View, Maybe<&2, W.WireRequest>, wire_of, H.Identity{left, left_context}, H.Identity{right, right_context}, same))
