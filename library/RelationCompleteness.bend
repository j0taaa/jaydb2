# Every actual matching SOURCE occurrence pair is retained at the unique
# independent left-prefix + right-prefix rank. Unmatched left occurrences
# receive exactly the single row rank zero, even when their values repeat.
import Base
import ./RelationRows.bend as Rows
import ./RelationNoMatches.bend as N
import ./RelationOuterRows.bend as Outer
import ./RelationModel.bend as M
import ./RelationAppendProofs.bend as Append
import ./SequencePaginationProofs.bend as Position
import ./SequenceSelectionProofs.bend as Selection
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ./Relation.bend as Relation
import ./Sequence.bend as Sequence
import ./Int64Proofs.bend as Arithmetic
import ../proof/Foundations.bend as F

law cons_prefix_rank_is_actual_row_length_plus_the_tail_rank:
  for ~left_key: D.Value -> String
  for ~right_key: D.Value -> String
  for +outer: Bool
  for +head: D.Value
  for +tail: List<&2,D.Value>
  for +right: List<&2,D.Value>
  for +index: Nat
  for +relative: Nat
  {Nat.add(M.before_left(~left_key,~right_key,outer,Con{head,tail},right,1n+index),relative) == Nat.add(Sequence.length(M.row(~left_key,~right_key,outer,head,right)),Nat.add(M.before_left(~left_key,~right_key,outer,tail,right,index),relative)) : Nat}
def cons_prefix_rank_is_actual_row_length_plus_the_tail_rank(left_key,right_key,outer,head,tail,right,index,relative):
  Equal.trans(Nat,Nat.add(Nat.add(M.row_count(~left_key,~right_key,outer,head,right),M.before_left(~left_key,~right_key,outer,tail,right,index)),relative),Nat.add(M.row_count(~left_key,~right_key,outer,head,right),Nat.add(M.before_left(~left_key,~right_key,outer,tail,right,index),relative)),Nat.add(Sequence.length(M.row(~left_key,~right_key,outer,head,right)),Nat.add(M.before_left(~left_key,~right_key,outer,tail,right,index),relative)),Arithmetic.add_associative(M.row_count(~left_key,~right_key,outer,head,right),M.before_left(~left_key,~right_key,outer,tail,right,index),relative),
    Equal.cong(Nat,Nat,n => Nat.add(n,Nat.add(M.before_left(~left_key,~right_key,outer,tail,right,index),relative)),M.row_count(~left_key,~right_key,outer,head,right),Sequence.length(M.row(~left_key,~right_key,outer,head,right)),Equal.sym(Nat,Sequence.length(M.row(~left_key,~right_key,outer,head,right)),M.row_count(~left_key,~right_key,outer,head,right),M.actual_row_length_is_its_independent_occurrence_weight(~left_key,~right_key,outer,head,right))))

law every_row_occurrence_is_retained_at_its_exact_left_major_rank:
  for ~left_key: D.Value -> String
  for ~right_key: D.Value -> String
  for +outer: Bool
  for +left: List<&2,D.Value>
  for +right: List<&2,D.Value>
  for +index: Nat
  for +value: D.Value
  for +relative: Nat
  for +payload: D.Value
  for present_left: {Position.at(left,index) == Some{value} : Maybe<&2,D.Value>}
  for present_row: {Position.at(M.row(~left_key,~right_key,outer,value,right),relative) == Some{payload} : Maybe<&2,D.Value>}
  {Position.at(M.run(~left_key,~right_key,outer,left,right),Nat.add(M.before_left(~left_key,~right_key,outer,left,right,index),relative)) == Some{payload} : Maybe<&2,D.Value>}
def every_row_occurrence_is_retained_at_its_exact_left_major_rank(left_key,right_key,outer,left,right,index,value,relative,payload,present_left,present_row):
  match left:
    case Nil{}: L.ex_false({Position.at(M.run(~left_key,~right_key,outer,Nil{},right),relative) == Some{payload} : Maybe<&2,D.Value>},F.none_negative_some(D.Value,value,present_left))
    case Con{+head,+tail}:
      match index:
        case 0n:
          Equal.trans(Maybe<&2,D.Value>,Position.at(M.run(~left_key,~right_key,outer,Con{head,tail},right),relative),Position.at(Relation.append(M.row(~left_key,~right_key,outer,head,right),M.run(~left_key,~right_key,outer,tail,right)),relative),Some{payload},
            Equal.cong(List<&2,D.Value>,Maybe<&2,D.Value>,items => Position.at(items,relative),M.run(~left_key,~right_key,outer,Con{head,tail},right),Relation.append(M.row(~left_key,~right_key,outer,head,right),M.run(~left_key,~right_key,outer,tail,right)),M.runtime_join_step_is_exact_row_then_remaining_left_sources(~left_key,~right_key,outer,head,tail,right)),
            Append.every_prefix_occurrence_keeps_its_exact_index_after_append(M.row(~left_key,~right_key,outer,head,right),M.run(~left_key,~right_key,outer,tail,right),relative,payload,
              Equal.trans(Maybe<&2,D.Value>,Position.at(M.row(~left_key,~right_key,outer,head,right),relative),Position.at(M.row(~left_key,~right_key,outer,value,right),relative),Some{payload},Equal.cong(D.Value,Maybe<&2,D.Value>,item => Position.at(M.row(~left_key,~right_key,outer,item,right),relative),head,value,Selection.equal_present_values_have_equal_payloads(head,value,present_left)),present_row)))
        case 1n+previous:
          Equal.trans(Maybe<&2,D.Value>,Position.at(M.run(~left_key,~right_key,outer,Con{head,tail},right),Nat.add(M.before_left(~left_key,~right_key,outer,Con{head,tail},right,1n+previous),relative)),Position.at(Relation.append(M.row(~left_key,~right_key,outer,head,right),M.run(~left_key,~right_key,outer,tail,right)),Nat.add(M.before_left(~left_key,~right_key,outer,Con{head,tail},right,1n+previous),relative)),Some{payload},
            Equal.cong(List<&2,D.Value>,Maybe<&2,D.Value>,items => Position.at(items,Nat.add(M.before_left(~left_key,~right_key,outer,Con{head,tail},right,1n+previous),relative)),M.run(~left_key,~right_key,outer,Con{head,tail},right),Relation.append(M.row(~left_key,~right_key,outer,head,right),M.run(~left_key,~right_key,outer,tail,right)),M.runtime_join_step_is_exact_row_then_remaining_left_sources(~left_key,~right_key,outer,head,tail,right)),
            Equal.trans(Maybe<&2,D.Value>,Position.at(Relation.append(M.row(~left_key,~right_key,outer,head,right),M.run(~left_key,~right_key,outer,tail,right)),Nat.add(M.before_left(~left_key,~right_key,outer,Con{head,tail},right,1n+previous),relative)),Position.at(Relation.append(M.row(~left_key,~right_key,outer,head,right),M.run(~left_key,~right_key,outer,tail,right)),Nat.add(Sequence.length(M.row(~left_key,~right_key,outer,head,right)),Nat.add(M.before_left(~left_key,~right_key,outer,tail,right,previous),relative))),Some{payload},
              Equal.cong(Nat,Maybe<&2,D.Value>,rank => Position.at(Relation.append(M.row(~left_key,~right_key,outer,head,right),M.run(~left_key,~right_key,outer,tail,right)),rank),Nat.add(M.before_left(~left_key,~right_key,outer,Con{head,tail},right,1n+previous),relative),Nat.add(Sequence.length(M.row(~left_key,~right_key,outer,head,right)),Nat.add(M.before_left(~left_key,~right_key,outer,tail,right,previous),relative)),cons_prefix_rank_is_actual_row_length_plus_the_tail_rank(~left_key,~right_key,outer,head,tail,right,previous,relative)),
              Append.every_suffix_occurrence_is_shifted_by_the_exact_prefix_length(M.row(~left_key,~right_key,outer,head,right),M.run(~left_key,~right_key,outer,tail,right),Nat.add(M.before_left(~left_key,~right_key,outer,tail,right,previous),relative),payload,every_row_occurrence_is_retained_at_its_exact_left_major_rank(~left_key,~right_key,outer,tail,right,previous,value,relative,payload,present_left,present_row))))

# No row-output, algorithm-result, or invariant premise: only the original
# source positions and ordinary key-match condition appear in this statement.
law every_matching_source_occurrence_pair_is_retained_at_its_exact_rank:
  for ~left_key: D.Value -> String
  for ~right_key: D.Value -> String
  for +outer: Bool
  for +left: List<&2,D.Value>
  for +right: List<&2,D.Value>
  for +left_index: Nat
  for +right_index: Nat
  for +left_value: D.Value
  for +right_value: D.Value
  for present_left: {Position.at(left,left_index) == Some{left_value} : Maybe<&2,D.Value>}
  for present_right: {Position.at(right,right_index) == Some{right_value} : Maybe<&2,D.Value>}
  for matched: {String.eq(left_key(left_value),right_key(right_value)) == True{} : Bool}
  {Position.at(M.run(~left_key,~right_key,outer,left,right),Nat.add(M.before_left(~left_key,~right_key,outer,left,right,left_index),Selection.before(~Rows.selected(~right_key),left_key(left_value),right,right_index))) == Some{Rows.pair(left_value,right_value)} : Maybe<&2,D.Value>}
def every_matching_source_occurrence_pair_is_retained_at_its_exact_rank(left_key,right_key,outer,left,right,left_index,right_index,left_value,right_value,present_left,present_right,matched):
  every_row_occurrence_is_retained_at_its_exact_left_major_rank(~left_key,~right_key,outer,left,right,left_index,left_value,Selection.before(~Rows.selected(~right_key),left_key(left_value),right,right_index),Rows.pair(left_value,right_value),present_left,M.every_matching_right_source_occurrence_is_retained_in_either_row_mode(~left_key,~right_key,outer,left_value,right,right_index,right_value,present_right,matched))

law every_unmatched_left_occurrence_has_its_single_absent_right_pair:
  for ~left_key: D.Value -> String
  for ~right_key: D.Value -> String
  for +left: List<&2,D.Value>
  for +right: List<&2,D.Value>
  for +index: Nat
  for +value: D.Value
  for present: {Position.at(left,index) == Some{value} : Maybe<&2,D.Value>}
  for zero: {Rows.count(~left_key,~right_key,value,right) == 0n : Nat}
  {Position.at(Relation.left_join(~left_key,~right_key,left,right),M.before_left(~left_key,~right_key,True{},left,right,index)) == Some{Rows.pair(value,D.VAbsent{})} : Maybe<&2,D.Value>}
def every_unmatched_left_occurrence_has_its_single_absent_right_pair(left_key,right_key,left,right,index,value,present,zero):
  %Arithmetic.add_zero_right(M.before_left(~left_key,~right_key,True{},left,right,index)) : {Position.at(Relation.left_join(~left_key,~right_key,left,right),_) == Some{Rows.pair(value,D.VAbsent{})} : Maybe<&2,D.Value>}
  every_row_occurrence_is_retained_at_its_exact_left_major_rank(~left_key,~right_key,True{},left,right,index,value,0n,Rows.pair(value,D.VAbsent{}),present,
    Equal.cong(List<&2,D.Value>,Maybe<&2,D.Value>,items => Position.at(items,0n),M.row(~left_key,~right_key,True{},value,right),[Rows.pair(value,D.VAbsent{})],M.unmatched_outer_row_is_exactly_one_absent_right_pair(~left_key,~right_key,value,right,zero)))

# Eliminating an unmatched source's origin proves uniqueness of the row rank
# and exact placeholder payload; a matching-index origin is contradictory.
law zero_match_rows_have_only_the_single_absent_origin:
  for ~left_key: D.Value -> String
  for ~right_key: D.Value -> String
  for +left: D.Value
  for +right: List<&2,D.Value>
  for +rank: Nat
  for +payload: D.Value
  for zero: {Rows.count(~left_key,~right_key,left,right) == 0n : Nat}
  for origin: Outer.Origin(~left_key,~right_key,left,right,rank,payload)
  N.Both<{rank == 0n : Nat},{payload == Rows.pair(left,D.VAbsent{}) : D.Value}>
def zero_match_rows_have_only_the_single_absent_origin(left_key,right_key,left,right,rank,payload,zero,origin):
  match origin:
    case L.Left{Tuple{+index,Tuple{+value,L.Both{present,L.Both{matched,rest}}}}}:
      F.absurd_boolean(N.Both<{rank == 0n : Nat},{payload == Rows.pair(left,D.VAbsent{}) : D.Value}>,Equal.trans(Bool,False{},String.eq(left_key(left),right_key(value)),True{},Equal.sym(Bool,String.eq(left_key(left),right_key(value)),False{},N.rejected_source_positions_have_nonmatching_keys(~left_key,~right_key,left,right,index,value,present,N.zero_matching_count_rejects_every_right_source_occurrence(~left_key,~right_key,left,right,zero))),matched))
    case L.Right{N.Both{unmatched,N.Both{at_zero,exact}}}: N.Both{at_zero,exact}
