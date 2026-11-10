# Complete mathematical correctness of the ACTUAL inner and left joins.
# All specifications use original indices, matching-prefix sums, exact payload
# encodings and source key equality. No output/permutation/order/invariant is
# assumed. Right VAbsent data and unmatched placeholders stay distinguishable
# by their source-index versus zero-match origins, even for equal payloads.
import Base
import ./RelationRows.bend as Rows
import ./RelationModel.bend as M
import ./RelationOrigins.bend as Origins
import ./RelationCompleteness.bend as Complete
import ./RelationOrder.bend as Order
import ./SequencePaginationProofs.bend as Position
import ./SequenceSelectionProofs.bend as Selection
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ./Relation.bend as Relation
import ./Sequence.bend as Sequence

def Missing(~left_key: D.Value -> String,~right_key: D.Value -> String,outer: Bool,+left: List<&2,D.Value>,+right: List<&2,D.Value>,+result: List<&2,D.Value>) -> Type:
  match outer:
    case False{}: Unit
    case True{}: @+index: Nat -> @+value: D.Value -> {Position.at(left,index) == Some{value} : Maybe<&2,D.Value>} -> {Rows.count(~left_key,~right_key,value,right) == 0n : Nat} -> {Position.at(result,M.before_left(~left_key,~right_key,True{},left,right,index)) == Some{Rows.pair(value,D.VAbsent{})} : Maybe<&2,D.Value>}

def LeftMajor(~left_key: D.Value -> String,~right_key: D.Value -> String,+outer: Bool,+left: List<&2,D.Value>,+right: List<&2,D.Value>) -> Type:
  @+first: Nat -> @+later: Nat -> @+value: D.Value -> @+relative: Nat -> @+later_relative: Nat -> {Position.at(left,first) == Some{value} : Maybe<&2,D.Value>} -> {Nat.is_lt(relative,M.row_count(~left_key,~right_key,outer,value,right)) == True{} : Bool} -> {Nat.is_lt(first,later) == True{} : Bool} -> {Nat.is_lt(Nat.add(M.before_left(~left_key,~right_key,outer,left,right,first),relative),Nat.add(M.before_left(~left_key,~right_key,outer,left,right,later),later_relative)) == True{} : Bool}

def RightMajor(~left_key: D.Value -> String,~right_key: D.Value -> String,+outer: Bool,+left: List<&2,D.Value>,+right: List<&2,D.Value>) -> Type:
  @+left_index: Nat -> @+left_value: D.Value -> @+first: Nat -> @+later: Nat -> @+right_value: D.Value -> {Position.at(right,first) == Some{right_value} : Maybe<&2,D.Value>} -> {String.eq(left_key(left_value),right_key(right_value)) == True{} : Bool} -> {Nat.is_lt(first,later) == True{} : Bool} -> {Nat.is_lt(Nat.add(M.before_left(~left_key,~right_key,outer,left,right,left_index),Selection.before(~Rows.selected(~right_key),left_key(left_value),right,first)),Nat.add(M.before_left(~left_key,~right_key,outer,left,right,left_index),Selection.before(~Rows.selected(~right_key),left_key(left_value),right,later))) == True{} : Bool}

def Meaning(~left_key: D.Value -> String,~right_key: D.Value -> String,+outer: Bool,+left: List<&2,D.Value>,+right: List<&2,D.Value>,+result: List<&2,D.Value>) -> Type:
  L.E<{Sequence.length(result) == M.total(~left_key,~right_key,outer,left,right) : Nat},
    L.E<@+rank: Nat -> @+payload: D.Value -> {Position.at(result,rank) == Some{payload} : Maybe<&2,D.Value>} -> M.Origin(~left_key,~right_key,outer,left,right,rank,payload),
      L.E<@+i: Nat -> @+j: Nat -> @+a: D.Value -> @+b: D.Value -> {Position.at(left,i) == Some{a} : Maybe<&2,D.Value>} -> {Position.at(right,j) == Some{b} : Maybe<&2,D.Value>} -> {String.eq(left_key(a),right_key(b)) == True{} : Bool} -> {Position.at(result,Nat.add(M.before_left(~left_key,~right_key,outer,left,right,i),Selection.before(~Rows.selected(~right_key),left_key(a),right,j))) == Some{Rows.pair(a,b)} : Maybe<&2,D.Value>},
        L.E<Missing(~left_key,~right_key,outer,left,right,result),L.E<LeftMajor(~left_key,~right_key,outer,left,right),RightMajor(~left_key,~right_key,outer,left,right)>>>>>


def missing_for_mode(~left_key: D.Value -> String,~right_key: D.Value -> String,outer: Bool,+left: List<&2,D.Value>,+right: List<&2,D.Value>) -> Missing(~left_key,~right_key,outer,left,right,M.run(~left_key,~right_key,outer,left,right)):
  match outer:
    case False{}: Unit{}
    case True{}: +index => +value => present => zero => Complete.every_unmatched_left_occurrence_has_its_single_absent_right_pair(~left_key,~right_key,left,right,index,value,present,zero)

law actual_joins_are_complete_ordered_source_occurrence_enumerations:
  for ~left_key: D.Value -> String
  for ~right_key: D.Value -> String
  for +outer: Bool
  for +left: List<&2,D.Value>
  for +right: List<&2,D.Value>
  Meaning(~left_key,~right_key,outer,left,right,M.run(~left_key,~right_key,outer,left,right))
def actual_joins_are_complete_ordered_source_occurrence_enumerations(left_key,right_key,outer,left,right):
  L.Both{Origins.actual_join_length_is_the_exact_sum_of_occurrence_weights(~left_key,~right_key,outer,left,right),L.Both{
    +rank => +payload => present => Origins.every_actual_join_output_has_exact_left_and_right_or_unmatched_source_indices(~left_key,~right_key,outer,left,right,rank,payload,present),
    L.Both{+i => +j => +a => +b => present_left => present_right => matched => Complete.every_matching_source_occurrence_pair_is_retained_at_its_exact_rank(~left_key,~right_key,outer,left,right,i,j,a,b,present_left,present_right,matched),
      L.Both{missing_for_mode(~left_key,~right_key,outer,left,right),L.Both{
        +first => +later => +value => +relative => +later_relative => present => inside => ordered => Order.every_earlier_left_row_occurrence_strictly_precedes_every_later_left_row_rank(~left_key,~right_key,outer,left,right,first,later,value,relative,later_relative,present,inside,ordered),
        +left_index => +left_value => +first => +later => +right_value => present => matched => ordered => Order.matching_right_occurrences_keep_their_strict_order_inside_the_same_left_prefix(~left_key,~right_key,outer,left,right,left_index,left_value,first,later,right_value,present,matched,ordered)}}}}}

law actual_inner_join_has_exact_matching_pair_occurrences_and_multiplicities:
  for ~left_key: D.Value -> String
  for ~right_key: D.Value -> String
  for +left: List<&2,D.Value>
  for +right: List<&2,D.Value>
  Meaning(~left_key,~right_key,False{},left,right,Relation.inner(~left_key,~right_key,left,right))
def actual_inner_join_has_exact_matching_pair_occurrences_and_multiplicities(left_key,right_key,left,right):
  actual_joins_are_complete_ordered_source_occurrence_enumerations(~left_key,~right_key,False{},left,right)

law actual_left_join_has_exact_matches_and_one_result_for_each_unmatched_occurrence:
  for ~left_key: D.Value -> String
  for ~right_key: D.Value -> String
  for +left: List<&2,D.Value>
  for +right: List<&2,D.Value>
  Meaning(~left_key,~right_key,True{},left,right,Relation.left_join(~left_key,~right_key,left,right))
def actual_left_join_has_exact_matches_and_one_result_for_each_unmatched_occurrence(left_key,right_key,left,right):
  actual_joins_are_complete_ordered_source_occurrence_enumerations(~left_key,~right_key,True{},left,right)
