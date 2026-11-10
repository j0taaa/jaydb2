# Per-entry and all-key completeness in the independent source-position filter
# model, not merely soundness of values that happen to survive grouping.
import Base
import ./SequenceGroupLookup.bend as Lookup
import ./SequenceGroupUniqueness.bend as U
import ./SequenceSelectionProofs.bend as Filter
import ./SequencePaginationProofs.bend as Position
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ./Sequence.bend as Sequence
import ../proof/Foundations.bend as F
import ../proof/Orders.bend as O

def group_key(group: Sequence.Group) -> String:
  Sequence.Group{key,items}=group
  key

def group_items(group: Sequence.Group) -> List<&2,D.Value>:
  Sequence.Group{key,items}=group
  items

def at_group(groups: List<&2,Sequence.Group>,index: Nat) -> Maybe<&2,Sequence.Group>:
  match groups:
    case Nil{}: None{}
    case Con{group,tail}:
      match index:
        case 0n: Some{group}
        case 1n+previous: at_group(tail,previous)

law present_group_equality_preserves_the_entire_entry:
  for +a: Sequence.Group
  for +b: Sequence.Group
  for same: {Some{a} == Some{b} : Maybe<&2,Sequence.Group>}
  {a == b : Sequence.Group}
def present_group_equality_preserves_the_entire_entry(a,b,same):
  Equal.cong(Maybe<&2,Sequence.Group>,Sequence.Group,result => F.extract_or(Sequence.Group,result,Sequence.Group{"",Nil{}}),Some{a},Some{b},same)

law absent_keys_differ_from_every_indexed_group_key:
  for +wanted: String
  for +groups: List<&2,Sequence.Group>
  for +index: Nat
  for +group: Sequence.Group
  for +present: {at_group(groups,index) == Some{group} : Maybe<&2,Sequence.Group>}
  for absent: U.Absent(wanted,groups)
  {String.eq(wanted,group_key(group)) == False{} : Bool}
def absent_keys_differ_from_every_indexed_group_key(wanted,groups,index,group,present,absent):
  match groups index absent:
    case Nil{} index Unit{}: L.ex_false({String.eq(wanted,group_key(group)) == False{} : Bool},F.none_negative_some(Sequence.Group,group,present))
    case Con{Sequence.Group{+head,+items},+tail} 0n U.Both{not_head,not_tail}:
      %present_group_equality_preserves_the_entire_entry(Sequence.Group{head,items},group,present) : {String.eq(wanted,group_key(_)) == False{} : Bool}
      not_head
    case Con{Sequence.Group{+head,+items},+tail} 1n+previous U.Both{not_head,not_tail}: absent_keys_differ_from_every_indexed_group_key(wanted,tail,previous,group,present,not_tail)

law every_unique_group_entry_is_observed_exactly_at_its_key:
  for +groups: List<&2,Sequence.Group>
  for +index: Nat
  for +group: Sequence.Group
  for +present: {at_group(groups,index) == Some{group} : Maybe<&2,Sequence.Group>}
  for unique: U.Unique(groups)
  {Lookup.lookup(group_key(group),groups) == Some{group_items(group)} : Maybe<&2,List<&2,D.Value>>}
def every_unique_group_entry_is_observed_exactly_at_its_key(groups,index,group,present,unique):
  match groups index unique:
    case Nil{} index Unit{}: L.ex_false({Lookup.lookup(group_key(group),Nil{}) == Some{group_items(group)} : Maybe<&2,List<&2,D.Value>>},F.none_negative_some(Sequence.Group,group,present))
    case Con{Sequence.Group{+head,+items},+tail} 0n U.Both{absent,+unique_tail}:
      %present_group_equality_preserves_the_entire_entry(Sequence.Group{head,items},group,present) : {Lookup.lookup(group_key(_),Con{Sequence.Group{head,items},tail}) == Some{group_items(_)} : Maybe<&2,List<&2,D.Value>>}
      Lookup.head_lookup_given(True{},head,head,items,tail,O.string_eq_refl(head))
    case Con{Sequence.Group{+head,+items},+tail} 1n+previous U.Both{absent,+unique_tail}:
      Equal.trans(Maybe<&2,List<&2,D.Value>>,Lookup.lookup(group_key(group),Con{Sequence.Group{head,items},tail}),Lookup.lookup(group_key(group),tail),Some{group_items(group)},Lookup.head_lookup_given(False{},group_key(group),head,items,tail,U.string_inequality_is_symmetric(head,group_key(group),absent_keys_differ_from_every_indexed_group_key(head,tail,previous,group,present,absent))),every_unique_group_entry_is_observed_exactly_at_its_key(tail,previous,group,present,unique_tail))

law a_present_representation_has_the_exact_payload:
  for +items: List<&2,D.Value>
  for +observed: List<&2,D.Value>
  for same: {Lookup.represented(items) == Some{observed} : Maybe<&2,List<&2,D.Value>>}
  {items == observed : List<&2,D.Value>}
def a_present_representation_has_the_exact_payload(items,observed,same):
  match items:
    case Nil{}: L.ex_false({Nil{} == observed : List<&2,D.Value>},F.none_negative_some(List<&2,D.Value>,observed,same))
    case Con{+head,+tail}: Equal.cong(Maybe<&2,List<&2,D.Value>>,List<&2,D.Value>,result => F.extract_or(List<&2,D.Value>,result,Nil{}),Some{Con{head,tail}},Some{observed},same)

law every_present_key_has_exact_independent_matching_occurrences_and_ranks:
  for ~key: D.Value -> String
  for +wanted: String
  for +xs: List<&2,D.Value>
  for +items: List<&2,D.Value>
  for observed: {Lookup.lookup(wanted,Sequence.group(~key,xs)) == Some{items} : Maybe<&2,List<&2,D.Value>>}
  Filter.Meaning(~Lookup.selected(~key),wanted,xs,items)
def every_present_key_has_exact_independent_matching_occurrences_and_ranks(key,wanted,xs,items,observed):
  %a_present_representation_has_the_exact_payload(Lookup.for_key(~key,wanted,xs),items,Equal.trans(Maybe<&2,List<&2,D.Value>>,Lookup.represented(Lookup.for_key(~key,wanted,xs)),Lookup.lookup(wanted,Sequence.group(~key,xs)),Some{items},Equal.sym(Maybe<&2,List<&2,D.Value>>,Lookup.lookup(wanted,Sequence.group(~key,xs)),Lookup.represented(Lookup.for_key(~key,wanted,xs)),Lookup.actual_group_lookup_is_exactly_all_original_matching_occurrences(~key,wanted,xs)),observed)) : Filter.Meaning(~Lookup.selected(~key),wanted,xs,_)
  Filter.actual_selection_is_exact_complete_and_ordered(~Lookup.selected(~key),wanted,xs)

law every_materialized_group_has_exact_original_members_in_original_order:
  for ~key: D.Value -> String
  for +xs: List<&2,D.Value>
  for +index: Nat
  for +group: Sequence.Group
  for present: {at_group(Sequence.group(~key,xs),index) == Some{group} : Maybe<&2,Sequence.Group>}
  Filter.Meaning(~Lookup.selected(~key),group_key(group),xs,group_items(group))
def every_materialized_group_has_exact_original_members_in_original_order(key,xs,index,group,present):
  every_present_key_has_exact_independent_matching_occurrences_and_ranks(~key,group_key(group),xs,group_items(group),every_unique_group_entry_is_observed_exactly_at_its_key(Sequence.group(~key,xs),index,group,present,U.actual_groups_have_unique_keys(~key,xs)))

def represented_when_any_position_is_present(+items: List<&2,D.Value>,index: Nat,+value: D.Value,present: {Position.at(items,index) == Some{value} : Maybe<&2,D.Value>}) ->
  {Lookup.represented(items) == Some{items} : Maybe<&2,List<&2,D.Value>>}:
  match items:
    case Nil{}: L.ex_false({None{} == Some{Nil{}} : Maybe<&2,List<&2,D.Value>>},F.none_negative_some(D.Value,value,present))
    case Con{head,tail}: {==}

law every_original_source_key_has_its_complete_materialized_group:
  for ~key: D.Value -> String
  for +xs: List<&2,D.Value>
  for +position: Nat
  for +value: D.Value
  for present: {Position.at(xs,position) == Some{value} : Maybe<&2,D.Value>}
  {Lookup.lookup(key(value),Sequence.group(~key,xs)) == Some{Lookup.for_key(~key,key(value),xs)} : Maybe<&2,List<&2,D.Value>>}
def every_original_source_key_has_its_complete_materialized_group(key,xs,position,value,present):
  Equal.trans(Maybe<&2,List<&2,D.Value>>,Lookup.lookup(key(value),Sequence.group(~key,xs)),Lookup.represented(Lookup.for_key(~key,key(value),xs)),Some{Lookup.for_key(~key,key(value),xs)},Lookup.actual_group_lookup_is_exactly_all_original_matching_occurrences(~key,key(value),xs),
    represented_when_any_position_is_present(Lookup.for_key(~key,key(value),xs),Filter.before(~Lookup.selected(~key),key(value),xs,position),value,Filter.every_matching_source_occurrence_is_retained_at_its_exact_rank(~Lookup.selected(~key),key(value),xs,position,value,present,O.string_eq_refl(key(value)))))

# No output, uniqueness, membership, permutation, or completeness assumption is
# required at this public boundary. All indexed source/output facts inside the
# specification are universal observations, not premises of the operation law.
def Meaning(~key: D.Value -> String,+xs: List<&2,D.Value>,+groups: List<&2,Sequence.Group>) -> Type:
  L.E<U.Unique(groups),L.E<U.NonemptyGroups(groups),
    L.E<@+wanted: String -> {Lookup.lookup(wanted,groups) == Lookup.represented(Lookup.for_key(~key,wanted,xs)) : Maybe<&2,List<&2,D.Value>>},
      @+index: Nat -> @+group: Sequence.Group -> {at_group(groups,index) == Some{group} : Maybe<&2,Sequence.Group>} -> Filter.Meaning(~Lookup.selected(~key),group_key(group),xs,group_items(group))>>>

law actual_group_has_unique_complete_keys_and_exact_ordered_members:
  for ~key: D.Value -> String
  for +xs: List<&2,D.Value>
  Meaning(~key,xs,Sequence.group(~key,xs))
def actual_group_has_unique_complete_keys_and_exact_ordered_members(key,xs):
  L.Both{U.actual_groups_have_unique_keys(~key,xs),L.Both{U.actual_groups_have_nonempty_member_lists(~key,xs),L.Both{
    +wanted => Lookup.actual_group_lookup_is_exactly_all_original_matching_occurrences(~key,wanted,xs),
    +index => +group => present => every_materialized_group_has_exact_original_members_in_original_order(~key,xs,index,group,present)}}}
