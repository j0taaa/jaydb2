# Actual event-query interpretation yields all observations in the extracted
# history, and inversion yields completeness. These are MODEL theorems, not a
# premise that the executable has a chosen trace or an unproved native Contract.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Interface.bend as I
import ../../../contract/Logic.bend as L
import ../../../contract/PreparedLaws.bend as H
import ../../../contract/Resources.bend as X
import ../../../contract/Semantics.bend as S
import ../../Foundations.bend as F
import ../../ProtocolService.bend as Q
import ../../SourceService.bend as Source
import ../specification/ServiceLaws.bend as E
import ../phases/PreparePhases.bend as V
import ../phases/InvalidationPhases.bend as N
import ./EventObserver.bend as O
import ./EventHistory.bend as T
import ./FrameBounds.bend as B
import ./MutationHistory.bend as M

def mutation(change: O.Change) -> E.Fact:
  O.Change{mode, mutation, before, after} = change
  E.Mutated{mode, mutation, before, after}

def impossible_change(-fact: E.Fact, -change: O.Change,
  found: {None{} == Some{change} : Maybe<&2, O.Change>}) -> {fact == mutation(change) : E.Fact}:
  L.ex_false({fact == mutation(change) : E.Fact}, F.none_negative_some(O.Change, change, found))

def phase_mutation(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +phase: V.PreparationEvent, -change: O.Change,
  found: {O.phase_change(phase) == Some{change} : Maybe<&2, O.Change>}) ->
  {V.fact(c, binding, public, phase) == mutation(change) : E.Fact}:
  match phase:
    case V.RegistryChanged{entry, before, after}:
      Equal.cong(O.Change, E.Fact, mutation, O.Change{True{}, E.Register{entry}, before, after}, change,
        F.some_injective(O.Change, O.Change{True{}, E.Register{entry}, before, after}, change, found))
    case V.WireReceived{wire}: impossible_change(V.fact(c, binding, public, phase), change, found)
    case V.IdentityEstablished{wire, context}: impossible_change(V.fact(c, binding, public, phase), change, found)
    case V.Accepted{wire, context}: impossible_change(V.fact(c, binding, public, phase), change, found)
    case V.Refuted{wire, context}: impossible_change(V.fact(c, binding, public, phase), change, found)
    case V.PrimitiveFailed{stage, identifier, fatal}: impossible_change(V.fact(c, binding, public, phase), change, found)
    case V.HandleChosen{handle}: impossible_change(V.fact(c, binding, public, phase), change, found)
    case V.ReceiptPrepared{receipt, bytes}: impossible_change(V.fact(c, binding, public, phase), change, found)
    case V.ArtifactSealed{entry}: impossible_change(V.fact(c, binding, public, phase), change, found)
    case V.ReceiptConcluded{receipt, result, snapshot, closes}: impossible_change(V.fact(c, binding, public, phase), change, found)
    case V.ErrorPrepared{status, bytes}: impossible_change(V.fact(c, binding, public, phase), change, found)
    case V.ErrorConcluded{status, snapshot, closes}: impossible_change(V.fact(c, binding, public, phase), change, found)
    case V.Delivered{bytes}: impossible_change(V.fact(c, binding, public, phase), change, found)
    case V.Interrupted{prefix}: impossible_change(V.fact(c, binding, public, phase), change, found)
    case V.Closed{}: impossible_change(V.fact(c, binding, public, phase), change, found)

law real_event_mutation_data_has_exact_full_fact_interpretation:
  for ~c: S.Configuration
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for +event: O.AuditEvent
  for -change: O.Change
  for found: {O.change(event) == Some{change} : Maybe<&2, O.Change>}
  {O.fact(c, binding, public, event) == mutation(change) : E.Fact}
def real_event_mutation_data_has_exact_full_fact_interpretation(c, binding, public, event, change, found):
  match event:
    case O.Core{mode, code, frame}: impossible_change(O.fact(c, binding, public, event), change, found)
    case O.BoundCore{mode, origin, frame}: impossible_change(O.fact(c, binding, public, event), change, found)
    case O.Preparation{phase}: phase_mutation(c, binding, public, phase, change, found)
    case O.Invalidation{N.InvalidationBase{phase}}: phase_mutation(c, binding, public, phase, change, found)
    case O.Invalidation{N.RegistryRemoved{handle, before, after}}:
      Equal.cong(O.Change, E.Fact, mutation, O.Change{True{}, E.Invalidate{handle}, before, after}, change,
        F.some_injective(O.Change, O.Change{True{}, E.Invalidate{handle}, before, after}, change, found))
    case O.Selection{snapshot}: impossible_change(O.fact(c, binding, public, event), change, found)
    case O.Resolution{raw, entry, context}: impossible_change(O.fact(c, binding, public, event), change, found)
    case O.Publication{mode, response, bytes, before, after}:
      Equal.cong(O.Change, E.Fact, mutation, O.Change{mode, E.Publish{response, bytes}, before, after}, change,
        F.some_injective(O.Change, O.Change{mode, E.Publish{response, bytes}, before, after}, change, found))

def ObservedRecord(~a: E.Environment, ~c: S.Configuration, k: String, record: E.Past) -> Type:
  E.Past{world, input, at, mode, mutation, +before, after} = record
  E.observes(a, k, I.Serve{world, c, E.database(before), input}, at, E.Mutated{mode, mutation, before, after})

def ObservedRecords(~a: E.Environment, ~c: S.Configuration, -k: String, records: List<&2, E.Past>) -> Type:
  match records:
    case Nil{}: Unit
    case Con{record, rest}: L.E<ObservedRecord(a, c, k, record), ObservedRecords(a, c, k, rest)>

def observe_change(~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~c: S.Configuration,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~items: List<&2, O.Item>, ~instance: String,
  +item: O.Item, +position: Nat, +change: O.Change, -previous: E.Snapshot,
  query: {B.query(O.Item, items, position) == Some{item} : Maybe<&2, O.Item>},
  found: {O.change(O.event(item)) == Some{change} : Maybe<&2, O.Change>},
  coherent: T.CoherentChange(Some{change}, item, previous)) ->
  ObservedRecord(O.environment(binding, public, c, seed, pi, artifacts, items, instance), c, Source.artifact(binding), T.record(change, item, O.time(position))):
  match item change coherent:
    case O.Item{+world, +selected, +input, +event} O.Change{mode, mutation, +before, after} L.Both{same, L.Both{scope, selected_same}}:
      L.Both{{==}, L.Right{(position, O.Item{world, selected, input, event},
        L.Both{{==}, L.Both{query, L.Both{
          Equal.cong(D.State, I.Scenario, state => I.Serve{world, c, state, input}, E.database(before), selected,
            Equal.sym(D.State, selected, E.database(before), selected_same)),
          L.Left{Equal.sym(E.Fact, O.fact(c, binding, public, event), E.Mutated{mode, mutation, before, after},
            real_event_mutation_data_has_exact_full_fact_interpretation(c, binding, public, event, O.Change{mode, mutation, before, after}, found))}}}})}}

def observed_step(~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~c: S.Configuration,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~items: List<&2, O.Item>, ~instance: String,
  option: Maybe<&2, O.Change>, +item: O.Item, +position: Nat, +rest: List<&2, E.Past>,
  -previous: E.Snapshot,
  exact: {O.change(O.event(item)) == option : Maybe<&2, O.Change>},
  query: {B.query(O.Item, items, position) == Some{item} : Maybe<&2, O.Item>},
  coherent: T.CoherentChange(option, item, previous),
  later: ObservedRecords(O.environment(binding, public, c, seed, pi, artifacts, items, instance), c, Source.artifact(binding), rest)) ->
  ObservedRecords(O.environment(binding, public, c, seed, pi, artifacts, items, instance), c, Source.artifact(binding), T.record_if(option, item, O.time(position), rest)):
  match option:
    case None{}: later
    case Some{change}:
      L.Both{observe_change(binding, public, c, seed, pi, artifacts, items, instance, item, position, change, previous, query, exact, coherent), later}

law canonical_queries_observe_every_actual_extracted_mutation:
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~c: S.Configuration
  for ~seed: Unit -> D.State
  for ~pi: String
  for ~artifacts: H.Artifacts
  for ~items: List<&2, O.Item>
  for ~instance: String
  for +prefix: List<&2, O.Item>
  for +position: Nat
  for +previous: E.Snapshot
  for coherent: T.Coherent(prefix, previous)
  for queries: T.Queries(items, prefix, position)
  ObservedRecords(O.environment(binding, public, c, seed, pi, artifacts, items, instance), c, Source.artifact(binding), T.extract(prefix, position))
def canonical_queries_observe_every_actual_extracted_mutation(binding, public, c, seed, pi, artifacts, items, instance, prefix, position, previous, coherent, queries):
  match prefix coherent queries:
    case Nil{} _ _: Unit{}
    case Con{+item, +rest} L.Both{first, later} L.Both{query, queries_rest}:
      observed_step(binding, public, c, seed, pi, artifacts, items, instance, O.change(O.event(item)), item, position, T.extract(rest, Succ{position}), previous,
        {==}, query, first, canonical_queries_observe_every_actual_extracted_mutation(binding, public, c, seed, pi, artifacts, items, instance, rest, Succ{position}, T.next(O.change(O.event(item)), previous), later, queries_rest))

law separate_event_results_derive_full_ordered_observed_history:
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~c: S.Configuration
  for ~seed: Unit -> D.State
  for ~pi: String
  for ~artifacts: H.Artifacts
  for ~items: List<&2, O.Item>
  for ~instance: String
  for records: List<&2, E.Past>
  for -previous: E.Snapshot
  for -lower: Nat
  for -upper: Nat
  for ordered: M.OrderedFrom(lower, records)
  for bounded: M.Before(upper, records)
  for linked: M.Linked(previous, records)
  for observed: ObservedRecords(O.environment(binding, public, c, seed, pi, artifacts, items, instance), c, Source.artifact(binding), records)
  E.HistoryObserved(O.environment(binding, public, c, seed, pi, artifacts, items, instance), Source.artifact(binding), c, records, previous, lower, upper, 0n)
def separate_event_results_derive_full_ordered_observed_history(binding, public, c, seed, pi, artifacts, items, instance, records, previous, lower, upper, ordered, bounded, linked, observed):
  match records ordered bounded linked observed:
    case Nil{} _ _ _ _: Unit{}
    case Con{E.Past{world, input, +at, mode, mutation, before, after}, +rest} L.Both{strict, ordered_rest} L.Both{inside, bounded_rest} L.Both{same, L.Both{scope, linked_rest}} L.Both{fact, observed_rest}:
      L.Both{{==}, L.Both{same, L.Both{scope, L.Both{strict, L.Both{inside, L.Both{fact,
        separate_event_results_derive_full_ordered_observed_history(binding, public, c, seed, pi, artifacts, items, instance, rest, after, at, upper, ordered_rest, bounded_rest, linked_rest, observed_rest)}}}}}}

def no_change_refutes(-other: E.Fact, -mode: Bool, -update: E.Mutation, -before: E.Snapshot, -after: E.Snapshot,
  no_change: {O.fact_change(other) == None{} : Maybe<&2, O.Change>},
  same: {E.Mutated{mode, update, before, after} == other : E.Fact}) -> Empty:
  F.none_negative_some(O.Change, O.Change{mode, update, before, after},
    Equal.sym(Maybe<&2, O.Change>, Some{O.Change{mode, update, before, after}}, None{},
      Equal.trans(Maybe<&2, O.Change>, Some{O.Change{mode, update, before, after}}, O.fact_change(other), None{},
        Equal.cong(E.Fact, Maybe<&2, O.Change>, O.fact_change, E.Mutated{mode, update, before, after}, other, same), no_change)))

def initial_fact_cannot_be_a_mutation(~c: S.Configuration, ~seed: Unit -> D.State, ~pi: String,
  -instance: String, at: Nat, -mode: Bool, -update: E.Mutation, -before: E.Snapshot, -after: E.Snapshot,
  observed: O.InitialFact(c, seed, pi, instance, at, E.Mutated{mode, update, before, after})) -> Empty:
  match at:
    case 0n: no_change_refutes(E.Ordinary{I.ProofInitialAccepts{}}, mode, update, before, after, {==}, observed)
    case 1n+k:
      match k:
        case 0n: no_change_refutes(E.Ordinary{I.InstanceStarted{seed(Unit{})}}, mode, update, before, after, {==}, observed)
        case 1n+j:
          match j:
            case 0n: no_change_refutes(E.Boot{E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}}, mode, update, before, after, {==}, observed)
            case 1n+rest: observed

def interpreted_mutation_recovers_exact_event_change(~c: S.Configuration, ~binding: Source.Source,
  ~public: List<&2, Source.FileSource>, +event: O.AuditEvent, -change: O.Change,
  same: {mutation(change) == O.fact(c, binding, public, event) : E.Fact}) ->
  {O.change(event) == O.fact_change(mutation(change)) : Maybe<&2, O.Change>}:
  Equal.sym(Maybe<&2, O.Change>, O.fact_change(mutation(change)), O.change(event),
    Equal.trans(Maybe<&2, O.Change>, O.fact_change(mutation(change)), O.fact_change(O.fact(c, binding, public, event)), O.change(event),
      Equal.cong(E.Fact, Maybe<&2, O.Change>, O.fact_change, mutation(change), O.fact(c, binding, public, event), same),
      O.interpreted_event_preserves_exact_mutation_data(c, binding, public, event)))

def core_fact_has_no_full_mutation(mode: Bool, -f: I.Fact) ->
  {O.fact_change(E.core_fact(mode, f)) == None{} : Maybe<&2, O.Change>}:
  match mode:
    case False{}: {==}
    case True{}: {==}

def publication_cofact_has_no_full_mutation(+event: O.AuditEvent, -f: E.Fact,
  cofact: O.PublicationFact(event, f)) -> {O.fact_change(f) == None{} : Maybe<&2, O.Change>}:
  match event:
    case O.Publication{+mode, response, bytes, before, +after}:
      Equal.trans(Maybe<&2, O.Change>, O.fact_change(f), O.fact_change(E.core_fact(mode, I.Published{E.database(after)})), None{},
        Equal.cong(E.Fact, Maybe<&2, O.Change>, O.fact_change, f, E.core_fact(mode, I.Published{E.database(after)}), cofact),
        core_fact_has_no_full_mutation(mode, I.Published{E.database(after)}))
    case O.Core{mode, code, frame}: L.ex_false({O.fact_change(f) == None{} : Maybe<&2, O.Change>}, cofact)
    case O.BoundCore{mode, origin, frame}: L.ex_false({O.fact_change(f) == None{} : Maybe<&2, O.Change>}, cofact)
    case O.Preparation{phase}: L.ex_false({O.fact_change(f) == None{} : Maybe<&2, O.Change>}, cofact)
    case O.Invalidation{event}: L.ex_false({O.fact_change(f) == None{} : Maybe<&2, O.Change>}, cofact)
    case O.Selection{snapshot}: L.ex_false({O.fact_change(f) == None{} : Maybe<&2, O.Change>}, cofact)
    case O.Resolution{raw, entry, context}: L.ex_false({O.fact_change(f) == None{} : Maybe<&2, O.Change>}, cofact)

def relational_mutation_recovers_exact_event_change(~c: S.Configuration, ~binding: Source.Source,
  ~public: List<&2, Source.FileSource>, +event: O.AuditEvent, -mode: Bool, -update: E.Mutation, -before: E.Snapshot, -after: E.Snapshot,
  relation: O.RelFact(c, binding, public, event, E.Mutated{mode, update, before, after})) ->
  {O.change(event) == Some{O.Change{mode, update, before, after}} : Maybe<&2, O.Change>}:
  match relation:
    case L.Left{same}: interpreted_mutation_recovers_exact_event_change(c, binding, public, event, O.Change{mode, update, before, after}, same)
    case L.Right{cofact}:
      L.ex_false({O.change(event) == Some{O.Change{mode, update, before, after}} : Maybe<&2, O.Change>},
        F.none_negative_some(O.Change, O.Change{mode, update, before, after},
          Equal.sym(Maybe<&2, O.Change>, Some{O.Change{mode, update, before, after}}, None{},
            publication_cofact_has_no_full_mutation(event, E.Mutated{mode, update, before, after}, cofact))))

def scenario_record(x: I.Scenario, change: O.Change, at: Nat) -> Maybe<&2, E.Past>:
  match x:
    case I.Initialize{world, c, seed, pi}: None{}
    case I.Serve{world, c, selected, input}: Some{T.record_change(change, world, input, at)}

def equal_scenario_recovers_exact_past(~c: S.Configuration, +item: O.Item, -x: I.Scenario,
  -change: O.Change, -at: Nat,
  same: {x == O.scenario(c, item) : I.Scenario}) ->
  {scenario_record(x, change, at) == Some{T.record(change, item, at)} : Maybe<&2, E.Past>}:
  match item:
    case O.Item{world, selected, input, event}:
      Equal.cong(I.Scenario, Maybe<&2, E.Past>, scenario => scenario_record(scenario, change, at),
        x, I.Serve{world, c, selected, input}, same)

def occurs_replace(-a: E.Past, -b: E.Past, -records: List<&2, E.Past>,
  equal: {a == b : E.Past}, occurs: E.Occurs(b, records)) -> E.Occurs(a, records):
  %Equal.sym(E.Past, a, b, equal) : E.Occurs(_, records)
  occurs

def SomeEqual(-A: Data, -a: A, value: Maybe<&2, A>) -> Type:
  match value:
    case None{}: Unit
    case Some{b}: {a == b : A}

def some_equality_is_injective_for_erased_indices(-A: Data, -a: A, -b: A,
  same: {Some{a} == Some{b} : Maybe<&2, A>}) -> {a == b : A}:
  %same : SomeEqual(A, a, _)
  {==}

def prefix_query_from_observed_time(+items: List<&2, O.Item>, +prefix: List<&2, O.Item>, +suffix: List<&2, O.Item>,
  +index: Nat, -item: O.Item, -at: Nat,
  decomposition: {items == T.append(prefix, suffix) : List<&2, O.Item>},
  same_time: {at == O.time(index) : Nat},
  earlier: {Nat.is_lt(at, O.time(B.count(O.Item, prefix))) == True{} : Bool},
  query: {B.query(O.Item, items, index) == Some{item} : Maybe<&2, O.Item>}) ->
  {B.query(O.Item, prefix, index) == Some{item} : Maybe<&2, O.Item>}:
  T.every_earlier_full_sequence_query_is_in_the_actual_prefix(prefix, suffix, index, item,
    Equal.trans(Bool, Nat.is_lt(O.time(index), O.time(B.count(O.Item, prefix))), Nat.is_lt(at, O.time(B.count(O.Item, prefix))), True{},
      Equal.cong(Nat, Bool, moment => Nat.is_lt(moment, O.time(B.count(O.Item, prefix))), O.time(index), at,
        Equal.sym(Nat, at, O.time(index), same_time)), earlier),
    Equal.trans(Maybe<&2, O.Item>, B.query(O.Item, T.append(prefix, suffix), index), B.query(O.Item, items, index), Some{item},
      Equal.cong(List<&2, O.Item>, Maybe<&2, O.Item>, source => B.query(O.Item, source, index), T.append(prefix, suffix), items,
        Equal.sym(List<&2, O.Item>, items, T.append(prefix, suffix), decomposition)), query))

def listed_complete_with_times(~c: S.Configuration, ~binding: Source.Source, ~public: List<&2, Source.FileSource>,
  +items: List<&2, O.Item>, +prefix: List<&2, O.Item>, +suffix: List<&2, O.Item>,
  -world: Nat, -input: X.Reception, -at: Nat, -mode: Bool, -mutation: E.Mutation, -before: E.Snapshot, -after: E.Snapshot,
  +index: Nat, +item: O.Item,
  decomposition: {items == T.append(prefix, suffix) : List<&2, O.Item>},
  time_copies: L.E<{at == O.time(index) : Nat}, {at == O.time(index) : Nat}>,
  earlier: {Nat.is_lt(at, O.time(B.count(O.Item, prefix))) == True{} : Bool},
  query: {B.query(O.Item, items, index) == Some{item} : Maybe<&2, O.Item>},
  scenario_same: {I.Serve{world, c, E.database(before), input} == O.scenario(c, item) : I.Scenario},
  fact_same: O.RelFact(c, binding, public, O.event(item), E.Mutated{mode, mutation, before, after})) ->
  E.Occurs(E.Past{world, input, at, mode, mutation, before, after}, T.extract(prefix, 0n)):
  match time_copies:
    case L.Both{for_bound, for_past}:
      occurs_replace(E.Past{world, input, at, mode, mutation, before, after}, T.record(O.Change{mode, mutation, before, after}, item, O.time(index)), T.extract(prefix, 0n),
        Equal.trans(E.Past, E.Past{world, input, at, mode, mutation, before, after}, T.record(O.Change{mode, mutation, before, after}, item, at), T.record(O.Change{mode, mutation, before, after}, item, O.time(index)),
          some_equality_is_injective_for_erased_indices(E.Past, E.Past{world, input, at, mode, mutation, before, after}, T.record(O.Change{mode, mutation, before, after}, item, at),
            equal_scenario_recovers_exact_past(c, item, I.Serve{world, c, E.database(before), input}, O.Change{mode, mutation, before, after}, at, scenario_same)),
          Equal.cong(Nat, E.Past, moment => T.record(O.Change{mode, mutation, before, after}, item, moment), at, O.time(index), for_past)),
        T.zero_start_actual_mutation_query_occurs_at_its_exact_event_time(prefix, index, item, O.Change{mode, mutation, before, after},
          prefix_query_from_observed_time(items, prefix, suffix, index, item, at, decomposition, for_bound, earlier, query),
          relational_mutation_recovers_exact_event_change(c, binding, public, O.event(item), mode, mutation, before, after, fact_same)))

law the_canonical_full_observer_cannot_hide_an_earlier_mutation:
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~c: S.Configuration
  for ~seed: Unit -> D.State
  for ~pi: String
  for ~artifacts: H.Artifacts
  for ~items: List<&2, O.Item>
  for ~instance: String
  for +prefix: List<&2, O.Item>
  for +suffix: List<&2, O.Item>
  for -world: Nat
  for -input: X.Reception
  for +at: Nat
  for -mode: Bool
  for -mutation: E.Mutation
  for -before: E.Snapshot
  for -after: E.Snapshot
  for decomposition: {items == T.append(prefix, suffix) : List<&2, O.Item>}
  for earlier: {Nat.is_lt(at, O.time(B.count(O.Item, prefix))) == True{} : Bool}
  for observed: E.observes(O.environment(binding, public, c, seed, pi, artifacts, items, instance), Source.artifact(binding),
    I.Serve{world, c, E.database(before), input}, at, E.Mutated{mode, mutation, before, after})
  E.Occurs(E.Past{world, input, at, mode, mutation, before, after}, T.extract(prefix, 0n))
def the_canonical_full_observer_cannot_hide_an_earlier_mutation(binding, public, c, seed, pi, artifacts, items, instance, prefix, suffix, world, input, at, mode, mutation, before, after, decomposition, earlier, observed):
  match observed:
    case L.Both{artifact, L.Left{L.Both{scenario, initial}}}:
      L.ex_false(E.Occurs(E.Past{world, input, at, mode, mutation, before, after}, T.extract(prefix, 0n)),
        initial_fact_cannot_be_a_mutation(c, seed, pi, instance, at, mode, mutation, before, after, initial))
    case L.Both{artifact, L.Right{(index, item, L.Both{same_time, L.Both{query, L.Both{scenario, fact}}})}}:
      listed_complete_with_times(c, binding, public, items, prefix, suffix, world, input, at, mode, mutation, before, after, index, item, decomposition,
        Q.equality_reopenable(Nat, at, O.time(index), same_time), earlier, query, scenario, fact)
