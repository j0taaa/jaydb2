# A left-join row has every matching occurrence, or exactly ONE absent-right
# pair when its independent matching count is zero. A real matching VAbsent
# keeps a source index via Rows.Origin; it is not mistaken for a placeholder.
import Base
import ./RelationRows.bend as Rows
import ./RelationNoMatches.bend as N
import ./SequencePaginationProofs.bend as Position
import ./SequenceSelectionProofs.bend as Selection
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ./Relation.bend as Relation
import ./Sequence.bend as Sequence
import ../proof/Foundations.bend as F

def weight(count: Nat) -> Nat:
  match count:
    case 0n: 1n
    case 1n+previous: 1n+previous

def Origin(~left_key: D.Value -> String,~right_key: D.Value -> String,+left: D.Value,+right: List<&2,D.Value>,+rank: Nat,+payload: D.Value) -> Type:
  L.Disjunction<Rows.Origin(~left_key,~right_key,left,right,rank,payload),
    N.Both<{Rows.count(~left_key,~right_key,left,right) == 0n : Nat},N.Both<{rank == 0n : Nat},{payload == Rows.pair(left,D.VAbsent{}) : D.Value}>>>

def Meaning(~left_key: D.Value -> String,~right_key: D.Value -> String,+left: D.Value,+right: List<&2,D.Value>,+result: List<&2,D.Value>) -> Type:
  L.E<{Sequence.length(result) == weight(Rows.count(~left_key,~right_key,left,right)) : Nat},
    L.E<@+rank: Nat -> @+payload: D.Value -> {Position.at(result,rank) == Some{payload} : Maybe<&2,D.Value>} -> Origin(~left_key,~right_key,left,right,rank,payload),
      L.E<@+index: Nat -> @+value: D.Value -> {Position.at(right,index) == Some{value} : Maybe<&2,D.Value>} -> {String.eq(left_key(left),right_key(value)) == True{} : Bool} -> {Position.at(result,Selection.before(~Rows.selected(~right_key),left_key(left),right,index)) == Some{Rows.pair(left,value)} : Maybe<&2,D.Value>},
        {Rows.count(~left_key,~right_key,left,right) == 0n : Nat} -> {result == [Rows.pair(left,D.VAbsent{})] : List<&2,D.Value>}>>>

def singleton_origin(~left_key: D.Value -> String,~right_key: D.Value -> String,+left: D.Value,+right: List<&2,D.Value>,rank: Nat,+payload: D.Value,present: {Position.at([Rows.pair(left,D.VAbsent{})],rank) == Some{payload} : Maybe<&2,D.Value>},zero: {Rows.count(~left_key,~right_key,left,right) == 0n : Nat}) -> Origin(~left_key,~right_key,left,right,rank,payload):
  match rank:
    case 0n: L.Right{N.Both{zero,N.Both{{==},Equal.sym(D.Value,Rows.pair(left,D.VAbsent{}),payload,Selection.equal_present_values_have_equal_payloads(Rows.pair(left,D.VAbsent{}),payload,present))}}}
    case 1n+previous: L.ex_false(Origin(~left_key,~right_key,left,right,1n+previous,payload),F.none_negative_some(D.Value,payload,present))

def positive_count_cannot_be_zero(-goal: Type,+tail: List<&2,D.Value>,+count: Nat,exact: {1n+Sequence.length(tail) == count : Nat},zero: {count == 0n : Nat}) -> goal:
  F.absurd_boolean(goal,Equal.cong(Nat,Bool,n => Nat.is_eq(n,0n),1n+Sequence.length(tail),0n,Equal.trans(Nat,1n+Sequence.length(tail),count,0n,exact,zero)))

# This dispatcher consumes each arbitrary Type function once; only literal
# Data count equality is copied for the independent result facts.
def row_case(~left_key: D.Value -> String,~right_key: D.Value -> String,+left: D.Value,+right: List<&2,D.Value>,found: List<&2,D.Value>,correct: Rows.Meaning(~left_key,~right_key,left,right,found)) -> Meaning(~left_key,~right_key,left,right,Relation.outer_matches(left,found)):
  match found correct:
    case Nil{} L.Both{+count,L.Both{origins,coverage}}:
      L.Both{Equal.cong(Nat,Nat,weight,0n,Rows.count(~left_key,~right_key,left,right),count),L.Both{
        +rank => +payload => present => singleton_origin(~left_key,~right_key,left,right,rank,payload,present,Equal.sym(Nat,0n,Rows.count(~left_key,~right_key,left,right),count)),
        L.Both{+index => +value => present => matched => L.ex_false({Position.at([Rows.pair(left,D.VAbsent{})],Selection.before(~Rows.selected(~right_key),left_key(left),right,index)) == Some{Rows.pair(left,value)} : Maybe<&2,D.Value>},F.none_negative_some(D.Value,Rows.pair(left,value),coverage(index,value,present,matched))),
          zero => {==}}}}
    case Con{+head,+tail} L.Both{+count,L.Both{origins,coverage}}:
      L.Both{Equal.cong(Nat,Nat,weight,1n+Sequence.length(tail),Rows.count(~left_key,~right_key,left,right),count),L.Both{
        +rank => +payload => present => L.Left{origins(rank,payload,present)},
        L.Both{+index => +value => present => matched => coverage(index,value,present,matched),
          zero => positive_count_cannot_be_zero({Con{head,tail} == [Rows.pair(left,D.VAbsent{})] : List<&2,D.Value>},tail,Rows.count(~left_key,~right_key,left,right),count,zero)}}}

law actual_outer_row_has_exact_matches_or_one_proved_unmatched_placeholder:
  for ~left_key: D.Value -> String
  for ~right_key: D.Value -> String
  for +left: D.Value
  for +right: List<&2,D.Value>
  Meaning(~left_key,~right_key,left,right,Relation.outer_matches(left,Relation.matches(~left_key,~right_key,left,right)))
def actual_outer_row_has_exact_matches_or_one_proved_unmatched_placeholder(left_key,right_key,left,right):
  row_case(~left_key,~right_key,left,right,Relation.matches(~left_key,~right_key,left,right),Rows.actual_matching_row_has_exact_occurrences_payloads_multiplicity_and_order(~left_key,~right_key,left,right))
