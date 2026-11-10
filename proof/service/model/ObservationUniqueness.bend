# Source-query inversion and structural uniqueness of selected DATA views.
# OnlyTag/NoTag are derived from concrete operational source constructors by
# callers. They are not primitive native uniqueness/Rule/observer hypotheses.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Interface.bend as I
import ../../../contract/Logic.bend as L
import ../../../contract/PreparedLaws.bend as H
import ../../../contract/Semantics.bend as S
import ../../Foundations.bend as F
import ../../ProtocolService.bend as Q
import ../../SourceService.bend as Source
import ../specification/ServiceLaws.bend as E
import ./EventObserver.bend as O
import ./FrameBounds.bend as B
import ./ObservedHistory.bend as R

type View is Data:
  VoidView{}
  SelectedView{snapshot: E.Snapshot}
  MutationView{prepared: Bool, mutation: E.Mutation, before: E.Snapshot, after: E.Snapshot}
  ConclusionView{outcome: E.Outcome, state: D.State, closes: Bool}
  PublicationView{state: D.State}

def view(fact: E.Fact) -> View:
  match fact:
    case E.Selected{snapshot}: SelectedView{snapshot}
    case E.Mutated{mode, mutation, before, after}: MutationView{mode, mutation, before, after}
    case E.PreparedKernel{I.Published{state}}: PublicationView{state}
    case E.PreparedKernel{I.Concluded{response, state, closes}}: ConclusionView{E.Transaction{response}, state, closes}
    case E.ReceiptConcluded{receipt, result, snapshot, closes}: ConclusionView{E.Receipt{receipt}, E.database(snapshot), closes}
    case _: VoidView{}

def tag(value: View) -> Nat:
  match value:
    case VoidView{}: 0n
    case SelectedView{snapshot}: 1n
    case MutationView{mode, mutation, before, after}: 2n
    case ConclusionView{outcome, state, closes}: 3n
    case PublicationView{state}: 4n

def Relevant(value: View) -> Type:
  match value:
    case VoidView{}: Empty
    case _: Unit

def Plain(event: O.AuditEvent) -> Type:
  match event:
    case O.Publication{mode, response, bytes, before, after}: Empty
    case _: Unit

def AllPlain(items: List<&2, O.Item>) -> Type:
  match items:
    case Nil{}: Unit
    case Con{item, rest}: L.E<Plain(O.event(item)), AllPlain(rest)>

def values(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, items: List<&2, O.Item>) -> List<&2, View>:
  match items:
    case Nil{}: Nil{}
    case Con{item, rest}: Con{view(O.fact(c, binding, public, O.event(item))), values(c, binding, public, rest)}

def NoTag(-kind: Nat, items: List<&2, View>) -> Type:
  match items:
    case Nil{}: Unit
    case Con{head, rest}: L.E<{Nat.is_eq(tag(head), kind) == False{} : Bool}, NoTag(kind, rest)>

def OnlyTag(-kind: Nat, items: List<&2, View>, index: Nat, -expected: View) -> Type:
  match items index:
    case Nil{} _: Empty
    case Con{+head, rest} 0n:
      L.E<{head == expected : View}, L.E<{tag(head) == kind : Nat}, NoTag(kind, rest)>>
    case Con{head, rest} 1n+k:
      L.E<{Nat.is_eq(tag(head), kind) == False{} : Bool}, OnlyTag(kind, rest, k, expected)>

law natural_equality_is_reflexive:
  for n: Nat
  {Nat.is_eq(n, n) == True{} : Bool}
def natural_equality_is_reflexive(n):
  match n:
    case 0n: {==}
    case 1n+k: natural_equality_is_reflexive(k)

def excluded_head(-head: View, -actual: View, +kind: Nat,
  different: {Nat.is_eq(tag(head), kind) == False{} : Bool},
  same: {head == actual : View}, wanted: {tag(actual) == kind : Nat}) -> Empty:
  F.false_negative_true(Equal.trans(Bool, False{}, Nat.is_eq(tag(head), kind), True{},
    Equal.sym(Bool, Nat.is_eq(tag(head), kind), False{}, different),
    Equal.trans(Bool, Nat.is_eq(tag(head), kind), Nat.is_eq(kind, kind), True{},
      Equal.cong(Nat, Bool, n => Nat.is_eq(n, kind), tag(head), kind,
        Equal.trans(Nat, tag(head), tag(actual), kind, Equal.cong(View, Nat, tag, head, actual, same), wanted)),
      natural_equality_is_reflexive(kind))))

law an_excluded_source_tag_cannot_be_queried:
  for +kind: Nat
  for items: List<&2, View>
  for index: Nat
  for -actual: View
  for excluded: NoTag(kind, items)
  for query: {B.query(View, items, index) == Some{actual} : Maybe<&2, View>}
  for wanted: {tag(actual) == kind : Nat}
  Empty
def an_excluded_source_tag_cannot_be_queried(kind, items, index, actual, excluded, query, wanted):
  match items index excluded:
    case Nil{} _ _: F.none_negative_some(View, actual, query)
    case Con{head, rest} 0n L.Both{first, later}:
      excluded_head(head, actual, kind, first, R.some_equality_is_injective_for_erased_indices(View, head, actual, query), wanted)
    case Con{head, rest} 1n+k L.Both{first, later}:
      an_excluded_source_tag_cannot_be_queried(kind, rest, k, actual, later, query, wanted)

def lift_equal_index(-index: Nat, -expected: Nat, -actual: View, -value: View,
  result: L.E<{index == expected : Nat}, {actual == value : View}>) ->
  L.E<{Succ{index} == Succ{expected} : Nat}, {actual == value : View}>:
  match result:
    case L.Both{same_index, same_value}: L.Both{Equal.cong(Nat, Nat, n => Succ{n}, index, expected, same_index), same_value}

law a_structurally_unique_source_tag_has_the_exact_index_and_payload:
  for +kind: Nat
  for items: List<&2, View>
  for expected_index: Nat
  for index: Nat
  for -expected: View
  for -actual: View
  for unique: OnlyTag(kind, items, expected_index, expected)
  for query: {B.query(View, items, index) == Some{actual} : Maybe<&2, View>}
  for wanted: {tag(actual) == kind : Nat}
  L.E<{index == expected_index : Nat}, {actual == expected : View}>
def a_structurally_unique_source_tag_has_the_exact_index_and_payload(kind, items, expected_index, index, expected, actual, unique, query, wanted):
  match items expected_index index unique:
    case Nil{} _ _ _:
      L.ex_false(L.E<{index == expected_index : Nat}, {actual == expected : View}>, unique)
    case Con{head, rest} 0n 0n L.Both{same, L.Both{head_tag, later}}:
      L.Both{{==}, Equal.trans(View, actual, head, expected,
        Equal.sym(View, head, actual, R.some_equality_is_injective_for_erased_indices(View, head, actual, query)), same)}
    case Con{head, rest} 0n 1n+k L.Both{same, L.Both{head_tag, later}}:
      L.ex_false(L.E<{Succ{k} == 0n : Nat}, {actual == expected : View}>,
        an_excluded_source_tag_cannot_be_queried(kind, rest, k, actual, later, query, wanted))
    case Con{head, rest} 1n+k 0n L.Both{different, later}:
      L.ex_false(L.E<{0n == Succ{k} : Nat}, {actual == expected : View}>,
        excluded_head(head, actual, kind, different, R.some_equality_is_injective_for_erased_indices(View, head, actual, query), wanted))
    case Con{head, rest} 1n+k 1n+j L.Both{different, later}:
      lift_equal_index(j, k, actual, expected,
        a_structurally_unique_source_tag_has_the_exact_index_and_payload(kind, rest, k, j, expected, actual, later, query, wanted))

def plain_query(items: List<&2, O.Item>, index: Nat, -item: O.Item,
  all: AllPlain(items), query: {B.query(O.Item, items, index) == Some{item} : Maybe<&2, O.Item>}) -> Plain(O.event(item)):
  match items index all:
    case Nil{} _ _: L.ex_false(Plain(O.event(item)), F.none_negative_some(O.Item, item, query))
    case Con{head, rest} 0n L.Both{first, later}:
      %R.some_equality_is_injective_for_erased_indices(O.Item, head, item, query) : Plain(O.event(_))
      first
    case Con{head, rest} 1n+k L.Both{first, later}: plain_query(rest, k, item, later, query)

def plain_has_no_cofact(event: O.AuditEvent, -f: E.Fact, plain: Plain(event), cofact: O.PublicationFact(event, f)) -> Empty:
  match event:
    case O.Publication{mode, response, bytes, before, after}: plain
    case O.Core{mode, code, frame}: cofact
    case O.BoundCore{mode, origin, frame}: cofact
    case O.Preparation{phase}: cofact
    case O.Invalidation{phase}: cofact
    case O.Selection{snapshot}: cofact
    case O.Resolution{raw, entry, context}: cofact

def plain_relation(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +event: O.AuditEvent, -f: E.Fact, plain: Plain(event), relation: O.RelFact(c, binding, public, event, f)) ->
  {f == O.fact(c, binding, public, event) : E.Fact}:
  match relation:
    case L.Left{same}: same
    case L.Right{cofact}: L.ex_false({f == O.fact(c, binding, public, event) : E.Fact}, plain_has_no_cofact(event, f, plain, cofact))

def view_result(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>, item: Maybe<&2, O.Item>) -> Maybe<&2, View>:
  match item:
    case None{}: None{}
    case Some{item}: Some{view(O.fact(c, binding, public, O.event(item)))}

law source_view_queries_are_the_exact_map_of_full_item_queries:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for items: List<&2, O.Item>
  for index: Nat
  {B.query(View, values(c, binding, public, items), index) == view_result(c, binding, public, B.query(O.Item, items, index)) : Maybe<&2, View>}
def source_view_queries_are_the_exact_map_of_full_item_queries(c, binding, public, items, index):
  match items index:
    case Nil{} _: {==}
    case Con{item, rest} 0n: {==}
    case Con{item, rest} 1n+k: source_view_queries_are_the_exact_map_of_full_item_queries(c, binding, public, rest, k)

def initial_view_is_void(~c: S.Configuration, ~seed: Unit -> D.State, ~pi: String, -instance: String,
  at: Nat, -f: E.Fact, initial: O.InitialFact(c, seed, pi, instance, at, f)) -> {view(f) == VoidView{} : View}:
  match at:
    case 0n: Equal.cong(E.Fact, View, view, f, E.Ordinary{I.ProofInitialAccepts{}}, initial)
    case 1n+k:
      match k:
        case 0n: Equal.cong(E.Fact, View, view, f, E.Ordinary{I.InstanceStarted{seed(Unit{})}}, initial)
        case 1n+j:
          match j:
            case 0n: Equal.cong(E.Fact, View, view, f, E.Boot{E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}}, initial)
            case 1n+rest: L.ex_false({view(f) == VoidView{} : View}, initial)

def relevant_not_void(-value: View, relevant: Relevant(value), same: {value == VoidView{} : View}) -> Empty:
  %same : Relevant(_)
  relevant

def observed_listed_view_copies(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +items: List<&2, O.Item>, +index: Nat, +item: O.Item, -f: E.Fact, -value: View,
  all: AllPlain(items), queries: L.E<{B.query(O.Item, items, index) == Some{item} : Maybe<&2, O.Item>}, {B.query(O.Item, items, index) == Some{item} : Maybe<&2, O.Item>}>,
  projected: {view(f) == value : View}, relation: O.RelFact(c, binding, public, O.event(item), f)) ->
  {B.query(View, values(c, binding, public, items), index) == Some{value} : Maybe<&2, View>}:
  match queries:
    case L.Both{for_plain, for_query}:
      Equal.trans(Maybe<&2, View>, B.query(View, values(c, binding, public, items), index), Some{view(O.fact(c, binding, public, O.event(item)))}, Some{value},
        Equal.trans(Maybe<&2, View>, B.query(View, values(c, binding, public, items), index), view_result(c, binding, public, B.query(O.Item, items, index)), Some{view(O.fact(c, binding, public, O.event(item)))},
          source_view_queries_are_the_exact_map_of_full_item_queries(c, binding, public, items, index),
          Equal.cong(Maybe<&2, O.Item>, Maybe<&2, View>, result => view_result(c, binding, public, result), B.query(O.Item, items, index), Some{item}, for_query)),
        Equal.cong(View, Maybe<&2, View>, v => Some{v}, view(O.fact(c, binding, public, O.event(item))), value,
          Equal.trans(View, view(O.fact(c, binding, public, O.event(item))), view(f), value,
            Equal.sym(View, view(f), view(O.fact(c, binding, public, O.event(item))),
              Equal.cong(E.Fact, View, view, f, O.fact(c, binding, public, O.event(item)),
                plain_relation(c, binding, public, O.event(item), f, plain_query(items, index, item, all, for_plain), relation))), projected)))

def observed_listed_view(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +items: List<&2, O.Item>, +index: Nat, +item: O.Item, -f: E.Fact, -value: View,
  all: AllPlain(items), query: {B.query(O.Item, items, index) == Some{item} : Maybe<&2, O.Item>},
  projected: {view(f) == value : View}, relation: O.RelFact(c, binding, public, O.event(item), f)) ->
  {B.query(View, values(c, binding, public, items), index) == Some{value} : Maybe<&2, View>}:
  observed_listed_view_copies(c, binding, public, items, index, item, f, value, all,
    Q.equality_reopenable(Maybe<&2, O.Item>, B.query(O.Item, items, index), Some{item}, query), projected, relation)

law every_relevant_observation_has_its_exact_actual_source_view_query:
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~c: S.Configuration
  for ~seed: Unit -> D.State
  for ~pi: String
  for ~artifacts: H.Artifacts
  for ~items: List<&2, O.Item>
  for ~instance: String
  for -x: I.Scenario
  for +at: Nat
  for -f: E.Fact
  for -value: View
  for all: AllPlain(items)
  for relevant: Relevant(value)
  for projected: {view(f) == value : View}
  for observed: E.observes(O.environment(binding, public, c, seed, pi, artifacts, items, instance), Source.artifact(binding), x, at, f)
  (&index: Nat -> L.E<{at == O.time(index) : Nat}, {B.query(View, values(c, binding, public, items), index) == Some{value} : Maybe<&2, View>}>)
def every_relevant_observation_has_its_exact_actual_source_view_query(binding, public, c, seed, pi, artifacts, items, instance, x, at, f, value, all, relevant, projected, observed):
  match observed:
    case L.Both{artifact, L.Left{L.Both{scenario, initial}}}:
      L.ex_false(&index: Nat -> L.E<{at == O.time(index) : Nat}, {B.query(View, values(c, binding, public, items), index) == Some{value} : Maybe<&2, View>}>,
        relevant_not_void(value, relevant, Equal.trans(View, value, view(f), VoidView{}, Equal.sym(View, view(f), value, projected), initial_view_is_void(c, seed, pi, instance, at, f, initial))))
    case L.Both{artifact, L.Right{(+index, +item, L.Both{same_time, L.Both{query, L.Both{scenario, relation}}})}}:
      (index, L.Both{same_time, observed_listed_view(c, binding, public, items, index, item, f, value, all, query, projected, relation)})

def finish_unique(-at: Nat, -index: Nat, -expected_index: Nat, -actual: View, -expected: View,
  same_time: {at == O.time(index) : Nat}, result: L.E<{index == expected_index : Nat}, {actual == expected : View}>) ->
  L.E<{at == O.time(expected_index) : Nat}, {actual == expected : View}>:
  match result:
    case L.Both{same_index, same_value}:
      L.Both{Equal.trans(Nat, at, O.time(index), O.time(expected_index), same_time, Equal.cong(Nat, Nat, O.time, index, expected_index, same_index)), same_value}

def source_unique_observation(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +kind: Nat, +items: List<&2, O.Item>, +expected_index: Nat, -expected: View, -at: Nat, -actual: View,
  unique: OnlyTag(kind, values(c, binding, public, items), expected_index, expected),
  wanted: {tag(actual) == kind : Nat},
  found: &index: Nat -> L.E<{at == O.time(index) : Nat}, {B.query(View, values(c, binding, public, items), index) == Some{actual} : Maybe<&2, View>}>) ->
  L.E<{at == O.time(expected_index) : Nat}, {actual == expected : View}>:
  match found:
    case (index, L.Both{same_time, query}):
      finish_unique(at, index, expected_index, actual, expected, same_time,
        a_structurally_unique_source_tag_has_the_exact_index_and_payload(kind, values(c, binding, public, items), expected_index, index, expected, actual, unique, query, wanted))

law actual_observation_inherits_only_the_derived_source_uniqueness:
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~c: S.Configuration
  for ~seed: Unit -> D.State
  for ~pi: String
  for ~artifacts: H.Artifacts
  for ~items: List<&2, O.Item>
  for ~instance: String
  for +kind: Nat
  for +expected_index: Nat
  for -expected: View
  for -x: I.Scenario
  for +at: Nat
  for -f: E.Fact
  for -actual: View
  for all: AllPlain(items)
  for unique: OnlyTag(kind, values(c, binding, public, items), expected_index, expected)
  for relevant: Relevant(actual)
  for projected: {view(f) == actual : View}
  for wanted: {tag(actual) == kind : Nat}
  for observed: E.observes(O.environment(binding, public, c, seed, pi, artifacts, items, instance), Source.artifact(binding), x, at, f)
  L.E<{at == O.time(expected_index) : Nat}, {actual == expected : View}>
def actual_observation_inherits_only_the_derived_source_uniqueness(binding, public, c, seed, pi, artifacts, items, instance, kind, expected_index, expected, x, at, f, actual, all, unique, relevant, projected, wanted, observed):
  source_unique_observation(c, binding, public, kind, items, expected_index, expected, at, actual, unique, wanted,
    every_relevant_observation_has_its_exact_actual_source_view_query(binding, public, c, seed, pi, artifacts, items, instance, x, at, f, actual, all, relevant, projected, observed))

def source_excluded_observation(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +kind: Nat, +items: List<&2, O.Item>, -at: Nat, -actual: View,
  excluded: NoTag(kind, values(c, binding, public, items)), wanted: {tag(actual) == kind : Nat},
  found: &index: Nat -> L.E<{at == O.time(index) : Nat}, {B.query(View, values(c, binding, public, items), index) == Some{actual} : Maybe<&2, View>}>) -> Empty:
  match found:
    case (index, L.Both{same_time, query}): an_excluded_source_tag_cannot_be_queried(kind, values(c, binding, public, items), index, actual, excluded, query, wanted)

law actual_observation_cannot_invent_a_tag_absent_from_its_source:
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~c: S.Configuration
  for ~seed: Unit -> D.State
  for ~pi: String
  for ~artifacts: H.Artifacts
  for ~items: List<&2, O.Item>
  for ~instance: String
  for +kind: Nat
  for -x: I.Scenario
  for +at: Nat
  for -f: E.Fact
  for -actual: View
  for all: AllPlain(items)
  for excluded: NoTag(kind, values(c, binding, public, items))
  for relevant: Relevant(actual)
  for projected: {view(f) == actual : View}
  for wanted: {tag(actual) == kind : Nat}
  for observed: E.observes(O.environment(binding, public, c, seed, pi, artifacts, items, instance), Source.artifact(binding), x, at, f)
  Empty
def actual_observation_cannot_invent_a_tag_absent_from_its_source(binding, public, c, seed, pi, artifacts, items, instance, kind, x, at, f, actual, all, excluded, relevant, projected, wanted, observed):
  source_excluded_observation(c, binding, public, kind, items, at, actual, excluded, wanted,
    every_relevant_observation_has_its_exact_actual_source_view_query(binding, public, c, seed, pi, artifacts, items, instance, x, at, f, actual, all, relevant, projected, observed))
