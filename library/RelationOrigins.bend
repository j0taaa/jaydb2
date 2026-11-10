# Complete lengths and source-occurrence origins for BOTH actual joins.
# The origin stores the exact left source index, row-relative source origin,
# a relative rank inside the row, and the independent left-prefix offset.
import Base
import ./RelationRows.bend as Rows
import ./RelationModel.bend as M
import ./RelationAppendProofs.bend as Append
import ./SequencePaginationProofs.bend as Position
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ./Relation.bend as Relation
import ./Sequence.bend as Sequence
import ./Int64Proofs.bend as Arithmetic
import ../proof/Foundations.bend as F

law actual_join_length_is_the_exact_sum_of_occurrence_weights:
  for ~left_key: D.Value -> String
  for ~right_key: D.Value -> String
  for +outer: Bool
  for +left: List<&2,D.Value>
  for +right: List<&2,D.Value>
  {Sequence.length(M.run(~left_key,~right_key,outer,left,right)) == M.total(~left_key,~right_key,outer,left,right) : Nat}
def actual_join_length_is_the_exact_sum_of_occurrence_weights(left_key,right_key,outer,left,right):
  match left:
    case Nil{}: Equal.cong(List<&2,D.Value>,Nat,Sequence.length,M.run(~left_key,~right_key,outer,Nil{},right),Nil{},M.either_join_of_an_empty_left_source_is_empty(~left_key,~right_key,outer,right))
    case Con{+head,+tail}:
      Equal.trans(Nat,Sequence.length(M.run(~left_key,~right_key,outer,Con{head,tail},right)),Sequence.length(Relation.append(M.row(~left_key,~right_key,outer,head,right),M.run(~left_key,~right_key,outer,tail,right))),M.total(~left_key,~right_key,outer,Con{head,tail},right),
        Equal.cong(List<&2,D.Value>,Nat,Sequence.length,M.run(~left_key,~right_key,outer,Con{head,tail},right),Relation.append(M.row(~left_key,~right_key,outer,head,right),M.run(~left_key,~right_key,outer,tail,right)),M.runtime_join_step_is_exact_row_then_remaining_left_sources(~left_key,~right_key,outer,head,tail,right)),
        Equal.trans(Nat,Sequence.length(Relation.append(M.row(~left_key,~right_key,outer,head,right),M.run(~left_key,~right_key,outer,tail,right))),Nat.add(Sequence.length(M.row(~left_key,~right_key,outer,head,right)),Sequence.length(M.run(~left_key,~right_key,outer,tail,right))),M.total(~left_key,~right_key,outer,Con{head,tail},right),Append.append_length_is_the_sum_of_input_lengths(M.row(~left_key,~right_key,outer,head,right),M.run(~left_key,~right_key,outer,tail,right)),
          Equal.trans(Nat,Nat.add(Sequence.length(M.row(~left_key,~right_key,outer,head,right)),Sequence.length(M.run(~left_key,~right_key,outer,tail,right))),Nat.add(M.row_count(~left_key,~right_key,outer,head,right),Sequence.length(M.run(~left_key,~right_key,outer,tail,right))),M.total(~left_key,~right_key,outer,Con{head,tail},right),Equal.cong(Nat,Nat,count => Nat.add(count,Sequence.length(M.run(~left_key,~right_key,outer,tail,right))),Sequence.length(M.row(~left_key,~right_key,outer,head,right)),M.row_count(~left_key,~right_key,outer,head,right),M.actual_row_length_is_its_independent_occurrence_weight(~left_key,~right_key,outer,head,right)),
            Equal.cong(Nat,Nat,count => Nat.add(M.row_count(~left_key,~right_key,outer,head,right),count),Sequence.length(M.run(~left_key,~right_key,outer,tail,right)),M.total(~left_key,~right_key,outer,tail,right),actual_join_length_is_the_exact_sum_of_occurrence_weights(~left_key,~right_key,outer,tail,right)))))

# Splitting at append is purely positional; a suffix occurrence is shifted by
# the proven row length, then transported to its mathematical match weight.
def lift_tail_origin(~left_key: D.Value -> String,~right_key: D.Value -> String,+outer: Bool,+head: D.Value,+tail: List<&2,D.Value>,+right: List<&2,D.Value>,+rank: Nat,+relative: Nat,+payload: D.Value,
  shifted: {Nat.add(Sequence.length(M.row(~left_key,~right_key,outer,head,right)),relative) == rank : Nat},
  origin: M.Origin(~left_key,~right_key,outer,tail,right,relative,payload)) -> M.Origin(~left_key,~right_key,outer,Con{head,tail},right,rank,payload):
  match origin:
    case Tuple{+index,Tuple{+value,Tuple{+within,L.Both{present,L.Both{row,L.Both{inside,ranked}}}}}}:
      Tuple{1n+index,Tuple{value,Tuple{within,L.Both{present,L.Both{row,L.Both{inside,
        Equal.trans(Nat,Nat.add(Nat.add(M.row_count(~left_key,~right_key,outer,head,right),M.before_left(~left_key,~right_key,outer,tail,right,index)),within),Nat.add(M.row_count(~left_key,~right_key,outer,head,right),Nat.add(M.before_left(~left_key,~right_key,outer,tail,right,index),within)),rank,
          Arithmetic.add_associative(M.row_count(~left_key,~right_key,outer,head,right),M.before_left(~left_key,~right_key,outer,tail,right,index),within),
          Equal.trans(Nat,Nat.add(M.row_count(~left_key,~right_key,outer,head,right),Nat.add(M.before_left(~left_key,~right_key,outer,tail,right,index),within)),Nat.add(M.row_count(~left_key,~right_key,outer,head,right),relative),rank,Equal.cong(Nat,Nat,n => Nat.add(M.row_count(~left_key,~right_key,outer,head,right),n),Nat.add(M.before_left(~left_key,~right_key,outer,tail,right,index),within),relative,ranked),
            Equal.trans(Nat,Nat.add(M.row_count(~left_key,~right_key,outer,head,right),relative),Nat.add(Sequence.length(M.row(~left_key,~right_key,outer,head,right)),relative),rank,Equal.cong(Nat,Nat,n => Nat.add(n,relative),M.row_count(~left_key,~right_key,outer,head,right),Sequence.length(M.row(~left_key,~right_key,outer,head,right)),Equal.sym(Nat,Sequence.length(M.row(~left_key,~right_key,outer,head,right)),M.row_count(~left_key,~right_key,outer,head,right),M.actual_row_length_is_its_independent_occurrence_weight(~left_key,~right_key,outer,head,right))),shifted)))}}}}}}


def dispatch_append_origin(~left_key: D.Value -> String,~right_key: D.Value -> String,+outer: Bool,+head: D.Value,+tail: List<&2,D.Value>,+right: List<&2,D.Value>,+rank: Nat,+payload: D.Value,
  split: Append.Split(M.row(~left_key,~right_key,outer,head,right),M.run(~left_key,~right_key,outer,tail,right),rank,payload),
  recursive: @+rank: Nat -> @+payload: D.Value -> {Position.at(M.run(~left_key,~right_key,outer,tail,right),rank) == Some{payload} : Maybe<&2,D.Value>} -> M.Origin(~left_key,~right_key,outer,tail,right,rank,payload)) -> M.Origin(~left_key,~right_key,outer,Con{head,tail},right,rank,payload):
  match split:
    case L.Left{+present}:
      Tuple{0n,Tuple{head,Tuple{rank,L.Both{{==},L.Both{M.every_actual_row_output_has_its_exact_right_source_or_unmatched_origin(~left_key,~right_key,outer,head,right,rank,payload,present),L.Both{
        Equal.trans(Bool,Nat.is_lt(rank,M.row_count(~left_key,~right_key,outer,head,right)),Nat.is_lt(rank,Sequence.length(M.row(~left_key,~right_key,outer,head,right))),True{},Equal.cong(Nat,Bool,n => Nat.is_lt(rank,n),M.row_count(~left_key,~right_key,outer,head,right),Sequence.length(M.row(~left_key,~right_key,outer,head,right)),Equal.sym(Nat,Sequence.length(M.row(~left_key,~right_key,outer,head,right)),M.row_count(~left_key,~right_key,outer,head,right),M.actual_row_length_is_its_independent_occurrence_weight(~left_key,~right_key,outer,head,right))),Append.present_positions_are_strictly_inside_the_input_length(M.row(~left_key,~right_key,outer,head,right),rank,payload,present)),{==}}}}}}}
    case L.Right{Tuple{+relative,L.Both{shifted,present}}}: lift_tail_origin(~left_key,~right_key,outer,head,tail,right,rank,relative,payload,shifted,recursive(relative,payload,present))

law every_actual_join_output_has_exact_left_and_right_or_unmatched_source_indices:
  for ~left_key: D.Value -> String
  for ~right_key: D.Value -> String
  for +outer: Bool
  for +left: List<&2,D.Value>
  for +right: List<&2,D.Value>
  for +rank: Nat
  for +payload: D.Value
  for present: {Position.at(M.run(~left_key,~right_key,outer,left,right),rank) == Some{payload} : Maybe<&2,D.Value>}
  M.Origin(~left_key,~right_key,outer,left,right,rank,payload)
def every_actual_join_output_has_exact_left_and_right_or_unmatched_source_indices(left_key,right_key,outer,left,right,rank,payload,present):
  match left:
    case Nil{}: L.ex_false(M.Origin(~left_key,~right_key,outer,Nil{},right,rank,payload),F.none_negative_some(D.Value,payload,Equal.trans(Maybe<&2,D.Value>,None{},Position.at(M.run(~left_key,~right_key,outer,Nil{},right),rank),Some{payload},Equal.sym(Maybe<&2,D.Value>,Position.at(M.run(~left_key,~right_key,outer,Nil{},right),rank),None{},Equal.cong(List<&2,D.Value>,Maybe<&2,D.Value>,items => Position.at(items,rank),M.run(~left_key,~right_key,outer,Nil{},right),Nil{},M.either_join_of_an_empty_left_source_is_empty(~left_key,~right_key,outer,right))),present)))
    case Con{+head,+tail}:
      dispatch_append_origin(~left_key,~right_key,outer,head,tail,right,rank,payload,Append.every_appended_output_has_an_exact_prefix_or_shifted_suffix_origin(M.row(~left_key,~right_key,outer,head,right),M.run(~left_key,~right_key,outer,tail,right),rank,payload,
        Equal.trans(Maybe<&2,D.Value>,Position.at(Relation.append(M.row(~left_key,~right_key,outer,head,right),M.run(~left_key,~right_key,outer,tail,right)),rank),Position.at(M.run(~left_key,~right_key,outer,Con{head,tail},right),rank),Some{payload},Equal.sym(Maybe<&2,D.Value>,Position.at(M.run(~left_key,~right_key,outer,Con{head,tail},right),rank),Position.at(Relation.append(M.row(~left_key,~right_key,outer,head,right),M.run(~left_key,~right_key,outer,tail,right)),rank),Equal.cong(List<&2,D.Value>,Maybe<&2,D.Value>,items => Position.at(items,rank),M.run(~left_key,~right_key,outer,Con{head,tail},right),Relation.append(M.row(~left_key,~right_key,outer,head,right),M.run(~left_key,~right_key,outer,tail,right)),M.runtime_join_step_is_exact_row_then_remaining_left_sources(~left_key,~right_key,outer,head,tail,right))),present)),
        +relative => +value => at => every_actual_join_output_has_exact_left_and_right_or_unmatched_source_indices(~left_key,~right_key,outer,tail,right,relative,value,at))
