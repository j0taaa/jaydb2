# Complete mutation extraction from the canonical operational event model.
# Coherence below is only a local before-snapshot/semantic-call equality; it
# grants no validity, certification, law, arbitrary final state or native trace.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Interface.bend as I
import ../../../contract/Logic.bend as L
import ../../../contract/Resources.bend as X
import ../../../contract/Semantics.bend as S
import ../../Foundations.bend as F
import ../../ProtocolService.bend as Q
import ../specification/ServiceLaws.bend as E
import ./EventObserver.bend as O
import ./FrameBounds.bend as B
import ./MutationHistory.bend as M

def append(items: List<&2, O.Item>, suffix: List<&2, O.Item>) -> List<&2, O.Item>:
  match items:
    case Nil{}: suffix
    case Con{head, rest}: Con{head, append(rest, suffix)}

def take(count: Nat, items: List<&2, O.Item>) -> List<&2, O.Item>:
  match count items:
    case 0n _: Nil{}
    case 1n+k Nil{}: Nil{}
    case 1n+k Con{head, rest}: Con{head, take(k, rest)}

def drop(count: Nat, items: List<&2, O.Item>) -> List<&2, O.Item>:
  match count items:
    case 0n items: items
    case 1n+k Nil{}: Nil{}
    case 1n+k Con{head, rest}: drop(k, rest)

law taking_a_prefix_preserves_every_event_in_its_full_suffix:
  for +count: Nat
  for +items: List<&2, O.Item>
  {append(take(count, items), drop(count, items)) == items : List<&2, O.Item>}
def taking_a_prefix_preserves_every_event_in_its_full_suffix(count, items):
  match count items:
    case 0n _: {==}
    case 1n+k Nil{}: {==}
    case Succ{+k} Con{+head, +rest}:
      Equal.cong(List<&2, O.Item>, List<&2, O.Item>, xs => Con{head, xs}, append(take(k, rest), drop(k, rest)), rest,
        taking_a_prefix_preserves_every_event_in_its_full_suffix(k, rest))

def next(option: Maybe<&2, O.Change>, previous: E.Snapshot) -> E.Snapshot:
  match option:
    case None{}: previous
    case Some{O.Change{mode, mutation, before, after}}: after

def finish(items: List<&2, O.Item>, +previous: E.Snapshot) -> E.Snapshot:
  match items:
    case Nil{}: previous
    case Con{+item, rest}: finish(rest, next(O.change(O.event(item)), previous))

def record_change(change: O.Change, world: Nat, input: X.Reception, at: Nat) -> E.Past:
  O.Change{mode, mutation, before, after} = change
  E.Past{world, input, at, mode, mutation, before, after}

def record(change: O.Change, item: O.Item, at: Nat) -> E.Past:
  O.Item{world, selected, input, event} = item
  record_change(change, world, input, at)

def record_if(option: Maybe<&2, O.Change>, item: O.Item, at: Nat, rest: List<&2, E.Past>) -> List<&2, E.Past>:
  match option:
    case None{}: rest
    case Some{change}: Con{record(change, item, at), rest}

def extract(items: List<&2, O.Item>, +position: Nat) -> List<&2, E.Past>:
  match items:
    case Nil{}: Nil{}
    case Con{+item, rest}:
      record_if(O.change(O.event(item)), item, O.time(position), extract(rest, Succ{position}))

def CoherentChange(option: Maybe<&2, O.Change>, item: O.Item, -previous: E.Snapshot) -> Type:
  match option item:
    case None{} _: Unit
    case Some{O.Change{mode, mutation, +before, +after}} O.Item{world, selected, input, event}:
      L.E<{before == previous : E.Snapshot},
        L.E<{E.instance(before) == E.instance(after) : String}, {selected == E.database(before) : D.State}>>

def Coherent(items: List<&2, O.Item>, +previous: E.Snapshot) -> Type:
  match items:
    case Nil{}: Unit
    case Con{+item, rest}:
      L.E<CoherentChange(O.change(O.event(item)), item, previous), Coherent(rest, next(O.change(O.event(item)), previous))>

def cons_copies(-head: Type, -tail: Type, first: L.E<head, head>, later: L.E<tail, tail>) ->
  L.E<L.E<head, tail>, L.E<head, tail>>:
  match first later:
    case L.Both{a, b} L.Both{c, d}: L.Both{L.Both{a, c}, L.Both{b, d}}

def change_copy(option: Maybe<&2, O.Change>, +item: O.Item, -previous: E.Snapshot,
  proof: CoherentChange(option, item, previous)) -> L.E<CoherentChange(option, item, previous), CoherentChange(option, item, previous)>:
  match option item proof:
    case None{} _ _: L.Both{Unit{}, Unit{}}
    case Some{O.Change{mode, mutation, +before, +after}} O.Item{world, +selected, input, event} L.Both{same, L.Both{scope, selected_same}}:
      cons_copies({before == previous : E.Snapshot}, L.E<{E.instance(before) == E.instance(after) : String}, {selected == E.database(before) : D.State}>,
        Q.equality_reopenable(E.Snapshot, before, previous, same),
        cons_copies({E.instance(before) == E.instance(after) : String}, {selected == E.database(before) : D.State},
          Q.equality_reopenable(String, E.instance(before), E.instance(after), scope),
          Q.equality_reopenable(D.State, selected, E.database(before), selected_same)))

law exact_local_transition_equalities_can_be_reopened_without_copying_programs:
  for +items: List<&2, O.Item>
  for +previous: E.Snapshot
  for proof: Coherent(items, previous)
  L.E<Coherent(items, previous), Coherent(items, previous)>
def exact_local_transition_equalities_can_be_reopened_without_copying_programs(items, previous, proof):
  match items proof:
    case Nil{} _: L.Both{Unit{}, Unit{}}
    case Con{+item, +rest} L.Both{first, later}:
      cons_copies(CoherentChange(O.change(O.event(item)), item, previous), Coherent(rest, next(O.change(O.event(item)), previous)),
        change_copy(O.change(O.event(item)), item, previous, first),
        exact_local_transition_equalities_can_be_reopened_without_copying_programs(rest, next(O.change(O.event(item)), previous), later))

def replay_step(option: Maybe<&2, O.Change>, +item: O.Item, +position: Nat, +rest: List<&2, E.Past>,
  +previous: E.Snapshot, -final: E.Snapshot,
  later: {E.replay(rest, next(option, previous)) == final : E.Snapshot}) ->
  {E.replay(record_if(option, item, O.time(position), rest), previous) == final : E.Snapshot}:
  match option:
    case None{}: later
    case Some{O.Change{mode, mutation, before, after}}:
      match item:
        case O.Item{world, selected, input, event}: later

law complete_event_extraction_replays_the_exact_operational_snapshot:
  for +items: List<&2, O.Item>
  for +position: Nat
  for +previous: E.Snapshot
  {E.replay(extract(items, position), previous) == finish(items, previous) : E.Snapshot}
def complete_event_extraction_replays_the_exact_operational_snapshot(items, position, previous):
  match items:
    case Nil{}: {==}
    case Con{+item, +rest}:
      replay_step(O.change(O.event(item)), item, position, extract(rest, Succ{position}), previous,
        finish(rest, next(O.change(O.event(item)), previous)),
        complete_event_extraction_replays_the_exact_operational_snapshot(rest, Succ{position}, next(O.change(O.event(item)), previous)))

def linked_step(option: Maybe<&2, O.Change>, +item: O.Item, position: Nat, +rest: List<&2, E.Past>,
  -previous: E.Snapshot, coherent: CoherentChange(option, item, previous), linked: M.Linked(next(option, previous), rest)) ->
  M.Linked(previous, record_if(option, item, O.time(position), rest)):
  match option item coherent:
    case None{} _ _: linked
    case Some{O.Change{mode, mutation, before, after}} O.Item{world, selected, input, event} L.Both{same, L.Both{scope, selected_same}}:
      L.Both{same, L.Both{scope, linked}}

law local_transition_snapshots_derive_every_complete_history_link:
  for +items: List<&2, O.Item>
  for +position: Nat
  for +previous: E.Snapshot
  for coherent: Coherent(items, previous)
  M.Linked(previous, extract(items, position))
def local_transition_snapshots_derive_every_complete_history_link(items, position, previous, coherent):
  match items coherent:
    case Nil{} _: Unit{}
    case Con{+item, +rest} L.Both{first, later}:
      linked_step(O.change(O.event(item)), item, position, extract(rest, Succ{position}), previous, first,
        local_transition_snapshots_derive_every_complete_history_link(rest, Succ{position}, next(O.change(O.event(item)), previous), later))

def scope_step(option: Maybe<&2, O.Change>, item: O.Item, -previous: E.Snapshot, -final: E.Snapshot,
  coherent: CoherentChange(option, item, previous),
  later: {E.instance(final) == E.instance(next(option, previous)) : String}) ->
  {E.instance(final) == E.instance(previous) : String}:
  match option item coherent:
    case None{} _ _: later
    case Some{O.Change{mode, mutation, before, after}} O.Item{world, selected, input, event} L.Both{same, L.Both{scope, selected_same}}:
      Equal.trans(String, E.instance(final), E.instance(after), E.instance(previous), later,
        Equal.trans(String, E.instance(after), E.instance(before), E.instance(previous),
          Equal.sym(String, E.instance(before), E.instance(after), scope),
          Equal.cong(E.Snapshot, String, E.instance, before, previous, same)))

law local_phase_transitions_keep_the_same_semantic_instance:
  for +items: List<&2, O.Item>
  for +previous: E.Snapshot
  for coherent: Coherent(items, previous)
  {E.instance(finish(items, previous)) == E.instance(previous) : String}
def local_phase_transitions_keep_the_same_semantic_instance(items, previous, coherent):
  match items coherent:
    case Nil{} _: {==}
    case Con{+item, +rest} L.Both{first, later}:
      scope_step(O.change(O.event(item)), item, previous, finish(rest, next(O.change(O.event(item)), previous)), first,
        local_phase_transitions_keep_the_same_semantic_instance(rest, next(O.change(O.event(item)), previous), later))

def Queries(-items: List<&2, O.Item>, source: List<&2, O.Item>, +position: Nat) -> Type:
  match source:
    case Nil{}: Unit
    case Con{+item, rest}:
      L.E<{B.query(O.Item, items, position) == Some{item} : Maybe<&2, O.Item>}, Queries(items, rest, Succ{position})>

def lift_queries(+head: O.Item, +items: List<&2, O.Item>, source: List<&2, O.Item>, +position: Nat,
  queries: Queries(items, source, position)) -> Queries(Con{head, items}, source, Succ{position}):
  match source queries:
    case Nil{} _: Unit{}
    case Con{item, rest} L.Both{first, later}:
      L.Both{first, lift_queries(head, items, rest, Succ{position}, later)}

law every_real_prefix_event_has_its_exact_full_sequence_query:
  for +prefix: List<&2, O.Item>
  for +suffix: List<&2, O.Item>
  Queries(append(prefix, suffix), prefix, 0n)
def every_real_prefix_event_has_its_exact_full_sequence_query(prefix, suffix):
  match prefix:
    case Nil{}: Unit{}
    case Con{+item, +rest}:
      L.Both{{==}, lift_queries(item, append(rest, suffix), rest, 0n,
        every_real_prefix_event_has_its_exact_full_sequence_query(rest, suffix))}

law every_earlier_full_sequence_query_is_in_the_actual_prefix:
  for +prefix: List<&2, O.Item>
  for +suffix: List<&2, O.Item>
  for index: Nat
  for -item: O.Item
  for earlier: {Nat.is_lt(index, B.count(O.Item, prefix)) == True{} : Bool}
  for found: {B.query(O.Item, append(prefix, suffix), index) == Some{item} : Maybe<&2, O.Item>}
  {B.query(O.Item, prefix, index) == Some{item} : Maybe<&2, O.Item>}
def every_earlier_full_sequence_query_is_in_the_actual_prefix(prefix, suffix, index, item, earlier, found):
  match prefix index:
    case Nil{} 0n: F.absurd_boolean({None{} == Some{item} : Maybe<&2, O.Item>}, earlier)
    case Nil{} 1n+k: F.absurd_boolean({None{} == Some{item} : Maybe<&2, O.Item>}, earlier)
    case Con{head, rest} 0n: found
    case Con{head, rest} 1n+k:
      every_earlier_full_sequence_query_is_in_the_actual_prefix(rest, suffix, k, item, earlier, found)

def end(items: List<&2, O.Item>, position: Nat) -> Nat:
  match items:
    case Nil{}: position
    case Con{item, rest}: end(rest, Succ{position})

law end_advances_one_for_each_event:
  for items: List<&2, O.Item>
  for +position: Nat
  {end(items, Succ{position}) == Succ{end(items, position)} : Nat}
def end_advances_one_for_each_event(items, position):
  match items:
    case Nil{}: {==}
    case Con{item, rest}: end_advances_one_for_each_event(rest, Succ{position})

law zero_start_end_is_the_actual_event_count:
  for +items: List<&2, O.Item>
  {end(items, 0n) == B.count(O.Item, items) : Nat}
def zero_start_end_is_the_actual_event_count(items):
  match items:
    case Nil{}: {==}
    case Con{item, +rest}:
      Equal.trans(Nat, end(rest, 1n), Succ{end(rest, 0n)}, Succ{B.count(O.Item, rest)},
        end_advances_one_for_each_event(rest, 0n),
        Equal.cong(Nat, Nat, n => Succ{n}, end(rest, 0n), B.count(O.Item, rest), zero_start_end_is_the_actual_event_count(rest)))

def ordered_step(option: Maybe<&2, O.Change>, item: O.Item, +position: Nat, +rest: List<&2, E.Past>,
  later: M.OrderedFrom(O.time(position), rest)) ->
  M.OrderedFrom(Succ{Succ{position}}, record_if(option, item, O.time(position), rest)):
  match option:
    case None{}: M.weaken_start(Succ{Succ{position}}, rest, later)
    case Some{O.Change{mode, mutation, before, after}}:
      match item:
        case O.Item{world, selected, input, event}: L.Both{M.successor_is_strictly_after(Succ{Succ{position}}), later}

law every_extracted_event_has_its_strict_physical_position:
  for +items: List<&2, O.Item>
  for +position: Nat
  M.OrderedFrom(Succ{Succ{position}}, extract(items, position))
def every_extracted_event_has_its_strict_physical_position(items, position):
  match items:
    case Nil{}: Unit{}
    case Con{+item, +rest}:
      ordered_step(O.change(O.event(item)), item, position, extract(rest, Succ{position}),
        every_extracted_event_has_its_strict_physical_position(rest, Succ{position}))

def end_after_head(items: List<&2, O.Item>, +position: Nat) ->
  {Nat.is_lt(O.time(position), O.time(end(items, Succ{position}))) == True{} : Bool}:
  match items:
    case Nil{}: M.successor_is_strictly_after(position)
    case Con{item, +rest}:
      M.lower_strict_bound(position, end(rest, Succ{Succ{position}}), end_after_head(rest, Succ{position}))

def bounded_step(option: Maybe<&2, O.Change>, item: O.Item, position: Nat, rest: List<&2, E.Past>, -upper: Nat,
  first: {Nat.is_lt(O.time(position), upper) == True{} : Bool}, later: M.Before(upper, rest)) ->
  M.Before(upper, record_if(option, item, O.time(position), rest)):
  match option:
    case None{}: later
    case Some{O.Change{mode, mutation, before, after}}:
      match item:
        case O.Item{world, selected, input, event}: L.Both{first, later}

law complete_prefix_history_precedes_the_next_physical_position:
  for +items: List<&2, O.Item>
  for +position: Nat
  M.Before(O.time(end(items, position)), extract(items, position))
def complete_prefix_history_precedes_the_next_physical_position(items, position):
  match items:
    case Nil{}: Unit{}
    case Con{+item, +rest}:
      bounded_step(O.change(O.event(item)), item, position, extract(rest, Succ{position}), O.time(end(rest, Succ{position})),
        end_after_head(rest, position), complete_prefix_history_precedes_the_next_physical_position(rest, Succ{position}))

law addition_successor_right:
  for a: Nat
  for +b: Nat
  {Nat.add(a, Succ{b}) == Succ{Nat.add(a, b)} : Nat}
def addition_successor_right(a, b):
  match a:
    case 0n: {==}
    case 1n+k: Equal.cong(Nat, Nat, n => Succ{n}, Nat.add(k, Succ{b}), Succ{Nat.add(k, b)}, addition_successor_right(k, b))

law addition_zero_right:
  for a: Nat
  {Nat.add(a, 0n) == a : Nat}
def addition_zero_right(a):
  match a:
    case 0n: {==}
    case 1n+k: Equal.cong(Nat, Nat, n => Succ{n}, Nat.add(k, 0n), k, addition_zero_right(k))

def first_occurs(option: Maybe<&2, O.Change>, +item: O.Item, +at: Nat, +rest: List<&2, E.Past>, -change: O.Change,
  found: {option == Some{change} : Maybe<&2, O.Change>}) -> E.Occurs(record(change, item, at), record_if(option, item, at, rest)):
  %Equal.sym(Maybe<&2, O.Change>, option, Some{change}, found) :
    E.Occurs(record(change, item, at), record_if(_, item, at, rest))
  L.Left{{==}}

def equal_head_occurs(+head: O.Item, +item: O.Item, +at: Nat, +rest: List<&2, E.Past>, -change: O.Change,
  equal: L.E<{head == item : O.Item}, {head == item : O.Item}>,
  found: {O.change(O.event(item)) == Some{change} : Maybe<&2, O.Change>}) ->
  E.Occurs(record(change, item, at), record_if(O.change(O.event(head)), head, at, rest)):
  match equal:
    case L.Both{for_target, for_found}:
      %for_target : E.Occurs(record(change, _, at), record_if(O.change(O.event(head)), head, at, rest))
      first_occurs(O.change(O.event(head)), head, at, rest, change,
        Equal.trans(Maybe<&2, O.Change>, O.change(O.event(head)), O.change(O.event(item)), Some{change},
          Equal.cong(O.Item, Maybe<&2, O.Change>, i => O.change(O.event(i)), head, item, for_found), found))

def later_occurs(option: Maybe<&2, O.Change>, item: O.Item, at: Nat, +rest: List<&2, E.Past>, -past: E.Past,
  later: E.Occurs(past, rest)) -> E.Occurs(past, record_if(option, item, at, rest)):
  match option:
    case None{}: later
    case Some{change}: L.Right{later}

law an_actual_mutation_query_cannot_be_omitted_from_extraction:
  for +items: List<&2, O.Item>
  for +position: Nat
  for index: Nat
  for +item: O.Item
  for -change: O.Change
  for queried: {B.query(O.Item, items, index) == Some{item} : Maybe<&2, O.Item>}
  for found: {O.change(O.event(item)) == Some{change} : Maybe<&2, O.Change>}
  E.Occurs(record(change, item, O.time(Nat.add(index, position))), extract(items, position))
def an_actual_mutation_query_cannot_be_omitted_from_extraction(items, position, index, item, change, queried, found):
  match items index:
    case Nil{} _: L.ex_false(E.Occurs(record(change, item, O.time(Nat.add(index, position))), Nil{}), F.none_negative_some(O.Item, item, queried))
    case Con{+head, +rest} 0n:
      equal_head_occurs(head, item, O.time(position), extract(rest, Succ{position}), change,
        Q.equality_reopenable(O.Item, head, item, F.some_injective(O.Item, head, item, queried)), found)
    case Con{+head, +rest} Succ{+k}:
      %addition_successor_right(k, position) :
        E.Occurs(record(change, item, O.time(_)), extract(Con{head, rest}, position))
      later_occurs(O.change(O.event(head)), head, O.time(position), extract(rest, Succ{position}),
        record(change, item, O.time(Nat.add(k, Succ{position}))),
        an_actual_mutation_query_cannot_be_omitted_from_extraction(rest, Succ{position}, k, item, change, queried, found))

law zero_start_actual_mutation_query_occurs_at_its_exact_event_time:
  for +items: List<&2, O.Item>
  for +index: Nat
  for +item: O.Item
  for -change: O.Change
  for queried: {B.query(O.Item, items, index) == Some{item} : Maybe<&2, O.Item>}
  for found: {O.change(O.event(item)) == Some{change} : Maybe<&2, O.Change>}
  E.Occurs(record(change, item, O.time(index)), extract(items, 0n))
def zero_start_actual_mutation_query_occurs_at_its_exact_event_time(items, index, item, change, queried, found):
  %addition_zero_right(index) : E.Occurs(record(change, item, O.time(_)), extract(items, 0n))
  an_actual_mutation_query_cannot_be_omitted_from_extraction(items, 0n, index, item, change, queried, found)
