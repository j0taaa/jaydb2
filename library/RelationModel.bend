# One independent source-index/rank model for inner and left joins. Prefix
# counts sum mathematical match multiplicities before a LEFT source index;
# they contain no join output, output permutation, or loop invariant.
import Base
import ./RelationRows.bend as Rows
import ./RelationOuterRows.bend as Outer
import ./SequencePaginationProofs.bend as Position
import ./SequenceSelectionProofs.bend as Selection
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ./Relation.bend as Relation
import ./Sequence.bend as Sequence


def row(~left_key: D.Value -> String,~right_key: D.Value -> String,outer: Bool,+left: D.Value,+right: List<&2,D.Value>) -> List<&2,D.Value>:
  Bool.pick(List<&2,D.Value>,outer,Relation.outer_matches(left,Relation.matches(~left_key,~right_key,left,right)),Relation.matches(~left_key,~right_key,left,right))

def run(~left_key: D.Value -> String,~right_key: D.Value -> String,outer: Bool,+left: List<&2,D.Value>,+right: List<&2,D.Value>) -> List<&2,D.Value>:
  Bool.pick(List<&2,D.Value>,outer,Relation.left_join(~left_key,~right_key,left,right),Relation.inner(~left_key,~right_key,left,right))

def row_count(~left_key: D.Value -> String,~right_key: D.Value -> String,outer: Bool,+left: D.Value,right: List<&2,D.Value>) -> Nat:
  +count=Rows.count(~left_key,~right_key,left,right)
  Bool.pick(Nat,outer,Outer.weight(count),count)

def total(~left_key: D.Value -> String,~right_key: D.Value -> String,+outer: Bool,left: List<&2,D.Value>,+right: List<&2,D.Value>) -> Nat:
  match left:
    case Nil{}: 0n
    case Con{l,tail}: Nat.add(row_count(~left_key,~right_key,outer,l,right),total(~left_key,~right_key,outer,tail,right))

def before_left(~left_key: D.Value -> String,~right_key: D.Value -> String,+outer: Bool,left: List<&2,D.Value>,+right: List<&2,D.Value>,index: Nat) -> Nat:
  match left:
    case Nil{}: 0n
    case Con{l,tail}:
      match index:
        case 0n: 0n
        case 1n+previous: Nat.add(row_count(~left_key,~right_key,outer,l,right),before_left(~left_key,~right_key,outer,tail,right,previous))

def RowOrigin(~left_key: D.Value -> String,~right_key: D.Value -> String,outer: Bool,+left: D.Value,+right: List<&2,D.Value>,+rank: Nat,+payload: D.Value) -> Type:
  match outer:
    case True{}: Outer.Origin(~left_key,~right_key,left,right,rank,payload)
    case False{}: Rows.Origin(~left_key,~right_key,left,right,rank,payload)

def Origin(~left_key: D.Value -> String,~right_key: D.Value -> String,+outer: Bool,+left: List<&2,D.Value>,+right: List<&2,D.Value>,+rank: Nat,+payload: D.Value) -> Type:
  Exists(Nat,index => Exists(D.Value,value => Exists(Nat,relative =>
    L.E<{Position.at(left,index) == Some{value} : Maybe<&2,D.Value>},
      L.E<RowOrigin(~left_key,~right_key,outer,value,right,relative,payload),
        L.E<{Nat.is_lt(relative,row_count(~left_key,~right_key,outer,value,right)) == True{} : Bool},
          {Nat.add(before_left(~left_key,~right_key,outer,left,right,index),relative) == rank : Nat}>>>)))

law runtime_join_step_is_exact_row_then_remaining_left_sources:
  for ~left_key: D.Value -> String
  for ~right_key: D.Value -> String
  for +outer: Bool
  for +value: D.Value
  for +tail: List<&2,D.Value>
  for +right: List<&2,D.Value>
  {run(~left_key,~right_key,outer,Con{value,tail},right) == Relation.append(row(~left_key,~right_key,outer,value,right),run(~left_key,~right_key,outer,tail,right)) : List<&2,D.Value>}
def runtime_join_step_is_exact_row_then_remaining_left_sources(left_key,right_key,outer,value,tail,right):
  match outer:
    case True{}: {==}
    case False{}: {==}


def length_from_outer_meaning(~left_key: D.Value -> String,~right_key: D.Value -> String,+left: D.Value,+right: List<&2,D.Value>,correct: Outer.Meaning(~left_key,~right_key,left,right,row(~left_key,~right_key,True{},left,right))) -> {Sequence.length(row(~left_key,~right_key,True{},left,right)) == row_count(~left_key,~right_key,True{},left,right) : Nat}:
  match correct:
    case L.Both{count,rest}: count

law actual_row_length_is_its_independent_occurrence_weight:
  for ~left_key: D.Value -> String
  for ~right_key: D.Value -> String
  for +outer: Bool
  for +left: D.Value
  for +right: List<&2,D.Value>
  {Sequence.length(row(~left_key,~right_key,outer,left,right)) == row_count(~left_key,~right_key,outer,left,right) : Nat}
def actual_row_length_is_its_independent_occurrence_weight(left_key,right_key,outer,left,right):
  match outer:
    case True{}: length_from_outer_meaning(~left_key,~right_key,left,right,Outer.actual_outer_row_has_exact_matches_or_one_proved_unmatched_placeholder(~left_key,~right_key,left,right))
    case False{}: Rows.matching_row_length_is_exactly_the_number_of_matching_right_occurrences(~left_key,~right_key,left,right)

def origin_from_outer_meaning(~left_key: D.Value -> String,~right_key: D.Value -> String,+left: D.Value,+right: List<&2,D.Value>,+rank: Nat,+payload: D.Value,present: {Position.at(row(~left_key,~right_key,True{},left,right),rank) == Some{payload} : Maybe<&2,D.Value>},correct: Outer.Meaning(~left_key,~right_key,left,right,row(~left_key,~right_key,True{},left,right))) -> Outer.Origin(~left_key,~right_key,left,right,rank,payload):
  match correct:
    case L.Both{count,L.Both{origin,rest}}: origin(rank,payload,present)

law every_actual_row_output_has_its_exact_right_source_or_unmatched_origin:
  for ~left_key: D.Value -> String
  for ~right_key: D.Value -> String
  for +outer: Bool
  for +left: D.Value
  for +right: List<&2,D.Value>
  for +rank: Nat
  for +payload: D.Value
  for present: {Position.at(row(~left_key,~right_key,outer,left,right),rank) == Some{payload} : Maybe<&2,D.Value>}
  RowOrigin(~left_key,~right_key,outer,left,right,rank,payload)
def every_actual_row_output_has_its_exact_right_source_or_unmatched_origin(left_key,right_key,outer,left,right,rank,payload,present):
  match outer:
    case True{}: origin_from_outer_meaning(~left_key,~right_key,left,right,rank,payload,present,Outer.actual_outer_row_has_exact_matches_or_one_proved_unmatched_placeholder(~left_key,~right_key,left,right))
    case False{}: Rows.every_match_output_has_an_exact_matching_right_source_occurrence(~left_key,~right_key,left,right,rank,payload,present)

def coverage_from_outer_meaning(~left_key: D.Value -> String,~right_key: D.Value -> String,+left: D.Value,+right: List<&2,D.Value>,+index: Nat,+value: D.Value,present: {Position.at(right,index) == Some{value} : Maybe<&2,D.Value>},matched: {String.eq(left_key(left),right_key(value)) == True{} : Bool},correct: Outer.Meaning(~left_key,~right_key,left,right,row(~left_key,~right_key,True{},left,right))) -> {Position.at(row(~left_key,~right_key,True{},left,right),Selection.before(~Rows.selected(~right_key),left_key(left),right,index)) == Some{Rows.pair(left,value)} : Maybe<&2,D.Value>}:
  match correct:
    case L.Both{count,L.Both{origin,L.Both{coverage,missing}}}: coverage(index,value,present,matched)

law every_matching_right_source_occurrence_is_retained_in_either_row_mode:
  for ~left_key: D.Value -> String
  for ~right_key: D.Value -> String
  for +outer: Bool
  for +left: D.Value
  for +right: List<&2,D.Value>
  for +index: Nat
  for +value: D.Value
  for present: {Position.at(right,index) == Some{value} : Maybe<&2,D.Value>}
  for matched: {String.eq(left_key(left),right_key(value)) == True{} : Bool}
  {Position.at(row(~left_key,~right_key,outer,left,right),Selection.before(~Rows.selected(~right_key),left_key(left),right,index)) == Some{Rows.pair(left,value)} : Maybe<&2,D.Value>}
def every_matching_right_source_occurrence_is_retained_in_either_row_mode(left_key,right_key,outer,left,right,index,value,present,matched):
  match outer:
    case True{}: coverage_from_outer_meaning(~left_key,~right_key,left,right,index,value,present,matched,Outer.actual_outer_row_has_exact_matches_or_one_proved_unmatched_placeholder(~left_key,~right_key,left,right))
    case False{}: Rows.every_matching_right_source_occurrence_is_encoded_at_its_exact_rank(~left_key,~right_key,left,right,index,value,present,matched)

def singleton_from_outer_meaning(~left_key: D.Value -> String,~right_key: D.Value -> String,+left: D.Value,+right: List<&2,D.Value>,zero: {Rows.count(~left_key,~right_key,left,right) == 0n : Nat},correct: Outer.Meaning(~left_key,~right_key,left,right,row(~left_key,~right_key,True{},left,right))) -> {row(~left_key,~right_key,True{},left,right) == [Rows.pair(left,D.VAbsent{})] : List<&2,D.Value>}:
  match correct:
    case L.Both{count,L.Both{origin,L.Both{coverage,missing}}}: missing(zero)

law unmatched_outer_row_is_exactly_one_absent_right_pair:
  for ~left_key: D.Value -> String
  for ~right_key: D.Value -> String
  for +left: D.Value
  for +right: List<&2,D.Value>
  for zero: {Rows.count(~left_key,~right_key,left,right) == 0n : Nat}
  {row(~left_key,~right_key,True{},left,right) == [Rows.pair(left,D.VAbsent{})] : List<&2,D.Value>}
def unmatched_outer_row_is_exactly_one_absent_right_pair(left_key,right_key,left,right,zero):
  singleton_from_outer_meaning(~left_key,~right_key,left,right,zero,Outer.actual_outer_row_has_exact_matches_or_one_proved_unmatched_placeholder(~left_key,~right_key,left,right))

law either_join_of_an_empty_left_source_is_empty:
  for ~left_key: D.Value -> String
  for ~right_key: D.Value -> String
  for +outer: Bool
  for +right: List<&2,D.Value>
  {run(~left_key,~right_key,outer,Nil{},right) == Nil{} : List<&2,D.Value>}
def either_join_of_an_empty_left_source_is_empty(left_key,right_key,outer,right):
  match outer:
    case True{}: {==}
    case False{}: {==}
