# Independent index/length algebra for concatenation, used to compose rows
# into left-major joins. There is no join specification in this helper.
import Base
import ./SequencePaginationProofs.bend as Position
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ./Relation.bend as Relation
import ./Sequence.bend as Sequence
import ../proof/Foundations.bend as F

law append_length_is_the_sum_of_input_lengths:
  for +first: List<&2,D.Value>
  for +later: List<&2,D.Value>
  {Sequence.length(Relation.append(first,later)) == Nat.add(Sequence.length(first),Sequence.length(later)) : Nat}
def append_length_is_the_sum_of_input_lengths(first,later):
  match first:
    case Nil{}: {==}
    case Con{x,+tail}: Equal.cong(Nat,Nat,n => 1n+n,Sequence.length(Relation.append(tail,later)),Nat.add(Sequence.length(tail),Sequence.length(later)),append_length_is_the_sum_of_input_lengths(tail,later))

law every_prefix_occurrence_keeps_its_exact_index_after_append:
  for +first: List<&2,D.Value>
  for +later: List<&2,D.Value>
  for +index: Nat
  for +value: D.Value
  for present: {Position.at(first,index) == Some{value} : Maybe<&2,D.Value>}
  {Position.at(Relation.append(first,later),index) == Some{value} : Maybe<&2,D.Value>}
def every_prefix_occurrence_keeps_its_exact_index_after_append(first,later,index,value,present):
  match first:
    case Nil{}: L.ex_false({Position.at(later,index) == Some{value} : Maybe<&2,D.Value>},F.none_negative_some(D.Value,value,present))
    case Con{x,+tail}:
      match index:
        case 0n: present
        case 1n+previous: every_prefix_occurrence_keeps_its_exact_index_after_append(tail,later,previous,value,present)

law every_suffix_occurrence_is_shifted_by_the_exact_prefix_length:
  for +first: List<&2,D.Value>
  for +later: List<&2,D.Value>
  for +index: Nat
  for +value: D.Value
  for present: {Position.at(later,index) == Some{value} : Maybe<&2,D.Value>}
  {Position.at(Relation.append(first,later),Nat.add(Sequence.length(first),index)) == Some{value} : Maybe<&2,D.Value>}
def every_suffix_occurrence_is_shifted_by_the_exact_prefix_length(first,later,index,value,present):
  match first:
    case Nil{}: present
    case Con{x,+tail}: every_suffix_occurrence_is_shifted_by_the_exact_prefix_length(tail,later,index,value,present)

def Split(+first: List<&2,D.Value>,+later: List<&2,D.Value>,+index: Nat,+value: D.Value) -> Type:
  L.Disjunction<{Position.at(first,index) == Some{value} : Maybe<&2,D.Value>},
    Exists(Nat,relative => L.E<{Nat.add(Sequence.length(first),relative) == index : Nat},{Position.at(later,relative) == Some{value} : Maybe<&2,D.Value>}>)>

def lift_split(+x: D.Value,+first: List<&2,D.Value>,+later: List<&2,D.Value>,+index: Nat,+value: D.Value,split: Split(first,later,index,value)) -> Split(Con{x,first},later,1n+index,value):
  match split:
    case L.Left{present}: L.Left{present}
    case L.Right{Tuple{+relative,L.Both{offset,present}}}: L.Right{Tuple{relative,L.Both{Equal.cong(Nat,Nat,n => 1n+n,Nat.add(Sequence.length(first),relative),index,offset),present}}}

law every_appended_output_has_an_exact_prefix_or_shifted_suffix_origin:
  for +first: List<&2,D.Value>
  for +later: List<&2,D.Value>
  for +index: Nat
  for +value: D.Value
  for present: {Position.at(Relation.append(first,later),index) == Some{value} : Maybe<&2,D.Value>}
  Split(first,later,index,value)
def every_appended_output_has_an_exact_prefix_or_shifted_suffix_origin(first,later,index,value,present):
  match first:
    case Nil{}: L.Right{Tuple{index,L.Both{{==},present}}}
    case Con{+x,+tail}:
      match index:
        case 0n: L.Left{present}
        case 1n+previous: lift_split(x,tail,later,previous,value,every_appended_output_has_an_exact_prefix_or_shifted_suffix_origin(tail,later,previous,value,present))

law present_positions_are_strictly_inside_the_input_length:
  for +xs: List<&2,D.Value>
  for +index: Nat
  for +value: D.Value
  for present: {Position.at(xs,index) == Some{value} : Maybe<&2,D.Value>}
  {Nat.is_lt(index,Sequence.length(xs)) == True{} : Bool}
def present_positions_are_strictly_inside_the_input_length(xs,index,value,present):
  match xs:
    case Nil{}: L.ex_false({Nat.is_lt(index,0n) == True{} : Bool},F.none_negative_some(D.Value,value,present))
    case Con{x,+tail}:
      match index:
        case 0n: {==}
        case 1n+previous: present_positions_are_strictly_inside_the_input_length(tail,previous,value,present)
