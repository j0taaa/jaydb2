# A publication cofact is retained in the observer. It cannot impersonate a
# selection, full mutation or conclusion. Only for these three exact tags may
# the relevant view be recovered from the canonical Item fact without Plain.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Interface.bend as I
import ../../../../contract/Logic.bend as L
import ../../../../contract/Semantics.bend as S
import ../../../Foundations.bend as F
import ../../../SourceService.bend as Source
import ../../specification/ServiceLaws.bend as E
import ../../model/EventObserver.bend as O
import ../../model/ObservationUniqueness.bend as U
import ../../model/FrameBounds.bend as B

type CriticalKind is Data:
  SelectionKind{}
  MutationKind{}
  ConclusionKind{}

def tag(kind: CriticalKind) -> Nat:
  match kind:
    case SelectionKind{}: 1n
    case MutationKind{}: 2n
    case ConclusionKind{}: 3n

def cofact_value(+mode: Bool, state: D.State) ->
  {U.tag(U.view(E.core_fact(mode, I.Published{state}))) == Bool.pick(Nat, mode, 4n, 0n) : Nat}:
  match mode:
    case False{}: {==}
    case True{}: {==}

def cofact_absurd(-fact: E.Fact, absent: Empty) -> (&mode: Bool -> {U.tag(U.view(fact)) == Bool.pick(Nat, mode, 4n, 0n) : Nat}):
  L.ex_false(&mode: Bool -> {U.tag(U.view(fact)) == Bool.pick(Nat, mode, 4n, 0n) : Nat}, absent)


def cofact_tag(+event: O.AuditEvent, -fact: E.Fact, actual: O.PublicationFact(event, fact)) ->
  (&mode: Bool -> {U.tag(U.view(fact)) == Bool.pick(Nat, mode, 4n, 0n) : Nat}):
  match event:
    case O.Publication{+mode, response, bytes, before, +after}:
      (mode, Equal.trans(Nat, U.tag(U.view(fact)), U.tag(U.view(E.core_fact(mode, I.Published{E.database(after)}))), Bool.pick(Nat, mode, 4n, 0n),
        Equal.cong(E.Fact, Nat, f => U.tag(U.view(f)), fact, E.core_fact(mode, I.Published{E.database(after)}), actual), cofact_value(mode, E.database(after))))
    case O.Core{mode, code, frame}: cofact_absurd(fact, actual)
    case O.BoundCore{mode, origin, frame}: cofact_absurd(fact, actual)
    case O.Preparation{phase}: cofact_absurd(fact, actual)
    case O.Invalidation{event}: cofact_absurd(fact, actual)
    case O.Selection{snapshot}: cofact_absurd(fact, actual)
    case O.Resolution{raw, entry, context}: cofact_absurd(fact, actual)

def cofact_excluded(kind: CriticalKind, mode: Bool) -> {Nat.is_eq(Bool.pick(Nat, mode, 4n, 0n), tag(kind)) == False{} : Bool}:
  match kind mode:
    case SelectionKind{} False{}: {==}
    case SelectionKind{} True{}: {==}
    case MutationKind{} False{}: {==}
    case MutationKind{} True{}: {==}
    case ConclusionKind{} False{}: {==}
    case ConclusionKind{} True{}: {==}

def cannot_be_critical(+kind: CriticalKind, +mode: Bool, -actual: Nat,
  wanted: {actual == tag(kind) : Nat}, cofact: {actual == Bool.pick(Nat, mode, 4n, 0n) : Nat}) -> Empty:
  F.false_negative_true(Equal.trans(Bool, False{}, Nat.is_eq(Bool.pick(Nat, mode, 4n, 0n), tag(kind)), True{},
    Equal.sym(Bool, Nat.is_eq(Bool.pick(Nat, mode, 4n, 0n), tag(kind)), False{}, cofact_excluded(kind, mode)),
    Equal.trans(Bool, Nat.is_eq(Bool.pick(Nat, mode, 4n, 0n), tag(kind)), Nat.is_eq(tag(kind), tag(kind)), True{},
      Equal.cong(Nat, Bool, n => Nat.is_eq(n, tag(kind)), Bool.pick(Nat, mode, 4n, 0n), tag(kind),
        Equal.trans(Nat, Bool.pick(Nat, mode, 4n, 0n), actual, tag(kind), Equal.sym(Nat, actual, Bool.pick(Nat, mode, 4n, 0n), cofact), wanted)),
      U.natural_equality_is_reflexive(tag(kind)))))

def cofact_impossible(+kind: CriticalKind, -fact: E.Fact, wanted: {U.tag(U.view(fact)) == tag(kind) : Nat},
  proof: &mode: Bool -> {U.tag(U.view(fact)) == Bool.pick(Nat, mode, 4n, 0n) : Nat}) -> Empty:
  match proof:
    case (mode, cofact): cannot_be_critical(kind, mode, U.tag(U.view(fact)), wanted, cofact)

def relational_view(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +kind: CriticalKind, +event: O.AuditEvent, -fact: E.Fact,
  wanted: {U.tag(U.view(fact)) == tag(kind) : Nat}, relation: O.RelFact(c, binding, public, event, fact)) ->
  {U.view(O.fact(c, binding, public, event)) == U.view(fact) : U.View}:
  match relation:
    case L.Left{same}:
      Equal.sym(U.View, U.view(fact), U.view(O.fact(c, binding, public, event)), Equal.cong(E.Fact, U.View, U.view, fact, O.fact(c, binding, public, event), same))
    case L.Right{cofact}:
      L.ex_false({U.view(O.fact(c, binding, public, event)) == U.view(fact) : U.View},
        cofact_impossible(kind, fact, wanted, cofact_tag(event, fact, cofact)))

def actual_query(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +kind: CriticalKind, +items: List<&2, O.Item>, +index: Nat, +item: O.Item, -fact: E.Fact,
  wanted: {U.tag(U.view(fact)) == tag(kind) : Nat},
  query: {B.query(O.Item, items, index) == Some{item} : Maybe<&2, O.Item>}, relation: O.RelFact(c, binding, public, O.event(item), fact)) ->
  {B.query(U.View, U.values(c, binding, public, items), index) == Some{U.view(fact)} : Maybe<&2, U.View>}:
  Equal.trans(Maybe<&2, U.View>, B.query(U.View, U.values(c, binding, public, items), index),
    U.view_result(c, binding, public, B.query(O.Item, items, index)), Some{U.view(fact)},
    U.source_view_queries_are_the_exact_map_of_full_item_queries(c, binding, public, items, index),
    Equal.trans(Maybe<&2, U.View>, U.view_result(c, binding, public, B.query(O.Item, items, index)),
      Some{U.view(O.fact(c, binding, public, O.event(item)))}, Some{U.view(fact)},
      Equal.cong(Maybe<&2, O.Item>, Maybe<&2, U.View>, result => U.view_result(c, binding, public, result), B.query(O.Item, items, index), Some{item}, query),
      Equal.cong(U.View, Maybe<&2, U.View>, v => Some{v}, U.view(O.fact(c, binding, public, O.event(item))), U.view(fact),
        relational_view(c, binding, public, kind, O.event(item), fact, wanted, relation))))
