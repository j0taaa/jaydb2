# Invert a real query in the derived header grammar. It computes the precise
# local slot and entire header payload, without fairness or outcome premises.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../Foundations.bend as F
import ../../../model/EventObserver.bend as O
import ../../../model/FrameBounds.bend as B
import ../../../model/serial/Common.bend as C
import ./HeaderData.bend as H
import ./RuntimeBase.bend as Runtime


def event_relevant(+point: H.Point, +wire: W.WireRequest, +context: Maybe<&2, D.Context>, +event: O.AuditEvent,
  same: {H.event(event) == H.expected(point, wire, context) : H.View}) -> H.Relevant(H.event(event)):
  %Equal.sym(H.View, H.event(event), H.expected(point, wire, context), same) : H.Relevant(_)
  H.expected_relevant(point, wire, context)


def equal_head(+head: O.AuditEvent, +actual: O.AuditEvent, absent: H.NoHeader(head), same: {head == actual : O.AuditEvent}) -> H.NoHeader(actual):
  %same : H.NoHeader(_) absent


def excluded(+events: List<&2, O.AuditEvent>, index: Nat, +event: O.AuditEvent,
  absent: Runtime.All(events), found: {B.query(O.AuditEvent, events, index) == Some{event} : Maybe<&2, O.AuditEvent>}, relevant: H.Relevant(H.event(event))) -> Empty:
  match events index absent:
    case Nil{} index unit: F.none_negative_some(O.AuditEvent, event, found)
    case Con{+head, rest} 0n L.Both{first, later}:
      H.irrelevant(H.event(event), relevant, H.excluded(event, equal_head(head, event, first, F.some_injective(O.AuditEvent, head, event, found))))
    case Con{head, +rest} 1n+previous L.Both{first, later}: excluded(rest, previous, event, later, found, relevant)


def at_head(+head: O.AuditEvent, +actual: O.AuditEvent, +wanted: H.View, +expected: H.View,
  same: {head == actual : O.AuditEvent}, observed: {H.event(actual) == wanted : H.View}, source: {H.event(head) == expected : H.View}) -> {wanted == expected : H.View}:
  Equal.trans(H.View, wanted, H.event(actual), expected, Equal.sym(H.View, H.event(actual), wanted, observed),
    Equal.trans(H.View, H.event(actual), H.event(head), expected,
      Equal.sym(H.View, H.event(head), H.event(actual), Equal.cong(O.AuditEvent, H.View, H.event, head, actual, same)), source))


def first(+point: H.Point, +wanted_wire: W.WireRequest, +wanted_context: Maybe<&2, D.Context>, +wire: W.WireRequest, +context: Maybe<&2, D.Context>,
  same: {H.expected(point, wanted_wire, wanted_context) == H.Wire{wire} : H.View}) ->
  L.E<{0n == H.offset(point) : Nat}, {H.expected(point, wanted_wire, wanted_context) == H.expected(point, wire, context) : H.View}>:
  match point:
    case H.WirePoint{}: L.Both{{==}, same}
    case H.IdentityPoint{}:
      L.ex_false(L.E<{0n == 1n : Nat}, {H.Identity{wanted_wire, wanted_context} == H.Identity{wire, context} : H.View}>,
        F.false_negative_true(Equal.cong(H.View, Bool, H.is_wire, H.Identity{wanted_wire, wanted_context}, H.Wire{wire}, same)))


def second(+point: H.Point, +wanted_wire: W.WireRequest, +wanted_context: Maybe<&2, D.Context>, +wire: W.WireRequest, +context: Maybe<&2, D.Context>,
  same: {H.expected(point, wanted_wire, wanted_context) == H.Identity{wire, context} : H.View}) ->
  L.E<{1n == H.offset(point) : Nat}, {H.expected(point, wanted_wire, wanted_context) == H.expected(point, wire, context) : H.View}>:
  match point:
    case H.IdentityPoint{}: L.Both{{==}, same}
    case H.WirePoint{}:
      L.ex_false(L.E<{1n == 0n : Nat}, {H.Wire{wanted_wire} == H.Wire{wire} : H.View}>,
        F.false_negative_true(Equal.sym(Bool, True{}, False{}, Equal.cong(H.View, Bool, H.is_wire, H.Wire{wanted_wire}, H.Identity{wire, context}, same))))


def in_pair(+point: H.Point, +wanted_wire: W.WireRequest, +wanted_context: Maybe<&2, D.Context>, +wire: W.WireRequest, +context: Maybe<&2, D.Context>,
  +first_event: O.AuditEvent, +second_event: O.AuditEvent, +tail: List<&2, O.AuditEvent>, index: Nat, +event: O.AuditEvent,
  first_view: {H.event(first_event) == H.Wire{wire} : H.View}, second_view: {H.event(second_event) == H.Identity{wire, context} : H.View}, absent: Runtime.All(tail),
  found: {B.query(O.AuditEvent, Con{first_event, Con{second_event, tail}}, index) == Some{event} : Maybe<&2, O.AuditEvent>},
  observed: {H.event(event) == H.expected(point, wanted_wire, wanted_context) : H.View}) ->
  L.E<{index == H.offset(point) : Nat}, {H.expected(point, wanted_wire, wanted_context) == H.expected(point, wire, context) : H.View}>:
  match index:
    case 0n:
      first(point, wanted_wire, wanted_context, wire, context,
        at_head(first_event, event, H.expected(point, wanted_wire, wanted_context), H.Wire{wire}, F.some_injective(O.AuditEvent, first_event, event, found), observed, first_view))
    case 1n+rest:
      match rest:
        case 0n:
          second(point, wanted_wire, wanted_context, wire, context,
            at_head(second_event, event, H.expected(point, wanted_wire, wanted_context), H.Identity{wire, context}, F.some_injective(O.AuditEvent, second_event, event, found), observed, second_view))
        case 1n+previous:
          L.ex_false(L.E<{Succ{Succ{previous}} == H.offset(point) : Nat}, {H.expected(point, wanted_wire, wanted_context) == H.expected(point, wire, context) : H.View}>,
            excluded(tail, previous, event, absent, found, event_relevant(point, wanted_wire, wanted_context, event, observed)))


def lift(-index: Nat, -expected: Nat, -wanted: H.View, -actual: H.View,
  result: L.E<{index == expected : Nat}, {wanted == actual : H.View}>) -> L.E<{Succ{index} == Succ{expected} : Nat}, {wanted == actual : H.View}>:
  match result:
    case L.Both{at, payload}: L.Both{Equal.cong(Nat, Nat, n => Succ{n}, index, expected, at), payload}


def in_prefix(+point: H.Point, +wanted_wire: W.WireRequest, +wanted_context: Maybe<&2, D.Context>, +wire: W.WireRequest, +context: Maybe<&2, D.Context>,
  +prefix: List<&2, O.AuditEvent>, +first_event: O.AuditEvent, +second_event: O.AuditEvent, +tail: List<&2, O.AuditEvent>, index: Nat, +event: O.AuditEvent,
  prefix_absent: Runtime.All(prefix), first_view: {H.event(first_event) == H.Wire{wire} : H.View}, second_view: {H.event(second_event) == H.Identity{wire, context} : H.View}, absent: Runtime.All(tail),
  found: {B.query(O.AuditEvent, C.append(prefix, Con{first_event, Con{second_event, tail}}), index) == Some{event} : Maybe<&2, O.AuditEvent>},
  observed: {H.event(event) == H.expected(point, wanted_wire, wanted_context) : H.View}) ->
  L.E<{index == Nat.add(B.count(O.AuditEvent, prefix), H.offset(point)) : Nat}, {H.expected(point, wanted_wire, wanted_context) == H.expected(point, wire, context) : H.View}>:
  match prefix index prefix_absent:
    case Nil{} index unit: in_pair(point, wanted_wire, wanted_context, wire, context, first_event, second_event, tail, index, event, first_view, second_view, absent, found, observed)
    case Con{+head, +rest} 0n L.Both{first_absent, rest_absent}:
      L.ex_false(L.E<{0n == Succ{Nat.add(B.count(O.AuditEvent, rest), H.offset(point))} : Nat}, {H.expected(point, wanted_wire, wanted_context) == H.expected(point, wire, context) : H.View}>,
        H.irrelevant(H.event(event), event_relevant(point, wanted_wire, wanted_context, event, observed),
          H.excluded(event, equal_head(head, event, first_absent, F.some_injective(O.AuditEvent, head, event, found)))))
    case Con{head, +rest} 1n+previous L.Both{first_absent, rest_absent}:
      lift(previous, Nat.add(B.count(O.AuditEvent, rest), H.offset(point)), H.expected(point, wanted_wire, wanted_context), H.expected(point, wire, context),
        in_prefix(point, wanted_wire, wanted_context, wire, context, rest, first_event, second_event, tail, previous, event, rest_absent, first_view, second_view, absent, found, observed))
