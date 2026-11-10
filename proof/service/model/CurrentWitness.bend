# Full ServiceLaws.Current witness for the canonical operational event model.
# The event sequence itself is retained losslessly. Native correspondence and
# Laws1..8 remain separate: this theorem supplies no fabricated checker result,
# final validity or actual-executable trace equality as a premise.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Interface.bend as I
import ../../../contract/Logic.bend as L
import ../../../contract/PreparedLaws.bend as H
import ../../../contract/Resources.bend as X
import ../../../contract/Semantics.bend as S
import ../../ProtocolService.bend as Q
import ../../SourceService.bend as Source
import ../specification/ServiceLaws.bend as E
import ./EventObserver.bend as O
import ./EventHistory.bend as T
import ./ObservedHistory.bend as R
import ./FrameBounds.bend as B
import ./MutationHistory.bend as M

def Parts(~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~c: S.Configuration,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~items: List<&2, O.Item>, ~instance: String,
  -i: String, -snapshot: E.Snapshot, -at: Nat, -records: List<&2, E.Past>) -> Type:
  L.E<E.observes(O.environment(binding, public, c, seed, pi, artifacts, items, instance), Source.artifact(binding),
    I.Initialize{0n, c, seed(Unit{}), pi}, 2n, E.Boot{E.Snapshot{i, seed(Unit{}), Nil{}, Nil{}}}),
    L.E<E.HistoryObserved(O.environment(binding, public, c, seed, pi, artifacts, items, instance), Source.artifact(binding), c,
      records, E.Snapshot{i, seed(Unit{}), Nil{}, Nil{}}, 2n, at, 0n),
      L.E<E.HistoryComplete(O.environment(binding, public, c, seed, pi, artifacts, items, instance), Source.artifact(binding), c,
        i, 2n, at, records, 0n),
        {snapshot == E.replay(records, E.Snapshot{i, seed(Unit{}), Nil{}, Nil{}}) : E.Snapshot}>>>

def transport_instance_parts(~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~c: S.Configuration,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~items: List<&2, O.Item>, ~instance: String,
  -snapshot: E.Snapshot, -at: Nat, -records: List<&2, E.Past>,
  same: {E.instance(snapshot) == instance : String},
  parts: Parts(binding, public, c, seed, pi, artifacts, items, instance, instance, snapshot, at, records)) ->
  Parts(binding, public, c, seed, pi, artifacts, items, instance, E.instance(snapshot), snapshot, at, records):
  %Equal.sym(String, E.instance(snapshot), instance, same) :
    Parts(binding, public, c, seed, pi, artifacts, items, instance, _, snapshot, at, records)
  parts

def construct_current(~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~c: S.Configuration,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~items: List<&2, O.Item>, ~instance: String,
  -world: Nat, -input: X.Reception, -selected: D.State, +snapshot: E.Snapshot, +count: Nat, +records: List<&2, E.Past>,
  parts: Parts(binding, public, c, seed, pi, artifacts, items, instance, E.instance(snapshot), snapshot, O.time(count), records)) ->
  E.Current(O.environment(binding, public, c, seed, pi, artifacts, items, instance), Source.artifact(binding),
    I.Serve{world, c, selected, input}, O.time(count), snapshot):
  match parts:
    case L.Both{boot, L.Both{observed, L.Both{complete, replay}}}:
      (0n, seed(Unit{}), pi, 2n, records, L.Both{{==}, L.Both{boot, L.Both{{==}, L.Both{observed, L.Both{complete, replay}}}}})

def bounded_at_count(+prefix: List<&2, O.Item>) -> M.Before(O.time(B.count(O.Item, prefix)), T.extract(prefix, 0n)):
  %T.zero_start_end_is_the_actual_event_count(prefix) : M.Before(O.time(_), T.extract(prefix, 0n))
  T.complete_prefix_history_precedes_the_next_physical_position(prefix, 0n)

def queries_from_decomposition(+items: List<&2, O.Item>, +prefix: List<&2, O.Item>, +suffix: List<&2, O.Item>,
  same: {items == T.append(prefix, suffix) : List<&2, O.Item>}) -> T.Queries(items, prefix, 0n):
  %Equal.sym(List<&2, O.Item>, items, T.append(prefix, suffix), same) : T.Queries(_, prefix, 0n)
  T.every_real_prefix_event_has_its_exact_full_sequence_query(prefix, suffix)

def complete_from_decomposition(~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~c: S.Configuration,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~items: List<&2, O.Item>, ~instance: String,
  +prefix: List<&2, O.Item>, +suffix: List<&2, O.Item>,
  same: {items == T.append(prefix, suffix) : List<&2, O.Item>}) ->
  E.HistoryComplete(O.environment(binding, public, c, seed, pi, artifacts, items, instance), Source.artifact(binding), c,
    instance, 2n, O.time(B.count(O.Item, prefix)), T.extract(prefix, 0n), 0n):
  world => input => at => mode => mutation => before => after => grouping => scope => lower => upper => observed =>
    R.the_canonical_full_observer_cannot_hide_an_earlier_mutation(binding, public, c, seed, pi, artifacts, items, instance,
      prefix, suffix, world, input, at, mode, mutation, before, after, same, upper, observed)

def prefix_parts(~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~c: S.Configuration,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~items: List<&2, O.Item>, ~instance: String,
  +prefix: List<&2, O.Item>, +suffix: List<&2, O.Item>,
  coherences: L.E<T.Coherent(prefix, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}),
    T.Coherent(prefix, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})>,
  decompositions: L.E<{items == T.append(prefix, suffix) : List<&2, O.Item>}, {items == T.append(prefix, suffix) : List<&2, O.Item>}>) ->
  Parts(binding, public, c, seed, pi, artifacts, items, instance, instance, T.finish(prefix, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}), O.time(B.count(O.Item, prefix)), T.extract(prefix, 0n)):
  match coherences decompositions:
    case L.Both{for_links, for_observed} L.Both{for_queries, for_complete}:
      L.Both{L.Both{{==}, L.Left{L.Both{{==}, {==}}}},
        L.Both{R.separate_event_results_derive_full_ordered_observed_history(binding, public, c, seed, pi, artifacts, items, instance, T.extract(prefix, 0n),
          E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, 2n, O.time(B.count(O.Item, prefix)),
          T.every_extracted_event_has_its_strict_physical_position(prefix, 0n), bounded_at_count(prefix),
          T.local_transition_snapshots_derive_every_complete_history_link(prefix, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, for_links),
          R.canonical_queries_observe_every_actual_extracted_mutation(binding, public, c, seed, pi, artifacts, items, instance, prefix, 0n,
            E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, for_observed, queries_from_decomposition(items, prefix, suffix, for_queries))),
          L.Both{complete_from_decomposition(binding, public, c, seed, pi, artifacts, items, instance, prefix, suffix, for_complete),
            Equal.sym(E.Snapshot, E.replay(T.extract(prefix, 0n), E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}), T.finish(prefix, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}),
              T.complete_event_extraction_replays_the_exact_operational_snapshot(prefix, 0n, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}))}}}

def current_from_copies(~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~c: S.Configuration,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~items: List<&2, O.Item>, ~instance: String,
  +prefix: List<&2, O.Item>, +suffix: List<&2, O.Item>, -world: Nat, -input: X.Reception,
  copies: L.E<T.Coherent(prefix, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}), T.Coherent(prefix, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})>,
  decomposition: {items == T.append(prefix, suffix) : List<&2, O.Item>}) ->
  E.Current(O.environment(binding, public, c, seed, pi, artifacts, items, instance), Source.artifact(binding),
    I.Serve{world, c, E.database(T.finish(prefix, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), input}, O.time(B.count(O.Item, prefix)),
    T.finish(prefix, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})):
  match copies:
    case L.Both{for_scope, for_parts}:
      construct_current(binding, public, c, seed, pi, artifacts, items, instance,
        world, input, E.database(T.finish(prefix, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})),
        T.finish(prefix, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}), B.count(O.Item, prefix), T.extract(prefix, 0n),
        transport_instance_parts(binding, public, c, seed, pi, artifacts, items, instance,
          T.finish(prefix, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}), O.time(B.count(O.Item, prefix)), T.extract(prefix, 0n),
          T.local_phase_transitions_keep_the_same_semantic_instance(prefix, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, for_scope),
          prefix_parts(binding, public, c, seed, pi, artifacts, items, instance, prefix, suffix,
            T.exact_local_transition_equalities_can_be_reopened_without_copying_programs(prefix, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, for_parts),
            Q.equality_reopenable(List<&2, O.Item>, items, T.append(prefix, suffix), decomposition))))

law complete_current_is_derived_from_the_lossless_operational_event_prefix:
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
  for coherent: T.Coherent(prefix, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})
  for decomposition: {items == T.append(prefix, suffix) : List<&2, O.Item>}
  E.Current(O.environment(binding, public, c, seed, pi, artifacts, items, instance), Source.artifact(binding),
    I.Serve{world, c, E.database(T.finish(prefix, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), input}, O.time(B.count(O.Item, prefix)),
    T.finish(prefix, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}))
def complete_current_is_derived_from_the_lossless_operational_event_prefix(binding, public, c, seed, pi, artifacts, items, instance, prefix, suffix, world, input, coherent, decomposition):
  current_from_copies(binding, public, c, seed, pi, artifacts, items, instance, prefix, suffix, world, input,
    T.exact_local_transition_equalities_can_be_reopened_without_copying_programs(prefix, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, coherent), decomposition)
