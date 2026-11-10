# Zero independent matching count is equivalent to rejecting EVERY source
# occurrence. The certificate is Data conjunctions of literal Boolean facts,
# never an arbitrary Type function copied to reuse a conclusion.
import Base
import ./RelationRows.bend as Rows
import ./SequencePaginationProofs.bend as Position
import ./SequenceSelectionProofs.bend as Selection
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ./Sequence.bend as Sequence
import ../proof/Foundations.bend as F

type Both<-P: Data,-Q: Data> is Data:
  Both{left: P,right: Q}

def Rejected(~left_key: D.Value -> String,~right_key: D.Value -> String,+left: D.Value,right: List<&2,D.Value>) -> Data:
  match right:
    case Nil{}: Unit
    case Con{r,tail}: Both<{String.eq(left_key(left),right_key(r)) == False{} : Bool},Rejected(~left_key,~right_key,left,tail)>

def zero_tick_case(kept: Bool,+tail: Nat,zero: {Selection.tick(kept,tail) == 0n : Nat}) -> Both<{kept == False{} : Bool},{tail == 0n : Nat}>:
  match kept:
    case False{}: Both{{==},zero}
    case True{}: F.absurd_boolean(Both<{True{} == False{} : Bool},{tail == 0n : Nat}>,Equal.cong(Nat,Bool,n => Nat.is_eq(n,0n),1n+tail,0n,zero))

def rejected_tail_from_zero(~left_key: D.Value -> String,~right_key: D.Value -> String,+left: D.Value,+r: D.Value,+tail: List<&2,D.Value>,split: Both<{String.eq(left_key(left),right_key(r)) == False{} : Bool},{Rows.count(~left_key,~right_key,left,tail) == 0n : Nat}>,recursive: {Rows.count(~left_key,~right_key,left,tail) == 0n : Nat} -> Rejected(~left_key,~right_key,left,tail)) -> Rejected(~left_key,~right_key,left,Con{r,tail}):
  match split:
    case Both{head,rest}: Both{head,recursive(rest)}

law zero_matching_count_rejects_every_right_source_occurrence:
  for ~left_key: D.Value -> String
  for ~right_key: D.Value -> String
  for +left: D.Value
  for +right: List<&2,D.Value>
  for zero: {Rows.count(~left_key,~right_key,left,right) == 0n : Nat}
  Rejected(~left_key,~right_key,left,right)
def zero_matching_count_rejects_every_right_source_occurrence(left_key,right_key,left,right,zero):
  match right:
    case Nil{}: Unit{}
    case Con{+r,+tail}: rejected_tail_from_zero(~left_key,~right_key,left,r,tail,zero_tick_case(String.eq(left_key(left),right_key(r)),Rows.count(~left_key,~right_key,left,tail),zero),rest => zero_matching_count_rejects_every_right_source_occurrence(~left_key,~right_key,left,tail,rest))

law rejecting_every_right_source_occurrence_has_zero_matching_count:
  for ~left_key: D.Value -> String
  for ~right_key: D.Value -> String
  for +left: D.Value
  for +right: List<&2,D.Value>
  for rejected: Rejected(~left_key,~right_key,left,right)
  {Rows.count(~left_key,~right_key,left,right) == 0n : Nat}
def rejecting_every_right_source_occurrence_has_zero_matching_count(left_key,right_key,left,right,rejected):
  match right rejected:
    case Nil{} Unit{}: {==}
    case Con{+r,+tail} Both{head,rest}:
      Equal.trans(Nat,Rows.count(~left_key,~right_key,left,Con{r,tail}),Rows.count(~left_key,~right_key,left,tail),0n,Equal.cong(Bool,Nat,kept => Selection.tick(kept,Rows.count(~left_key,~right_key,left,tail)),String.eq(left_key(left),right_key(r)),False{},head),rejecting_every_right_source_occurrence_has_zero_matching_count(~left_key,~right_key,left,tail,rest))

law rejected_source_positions_have_nonmatching_keys:
  for ~left_key: D.Value -> String
  for ~right_key: D.Value -> String
  for +left: D.Value
  for +right: List<&2,D.Value>
  for +index: Nat
  for +value: D.Value
  for present: {Position.at(right,index) == Some{value} : Maybe<&2,D.Value>}
  for rejected: Rejected(~left_key,~right_key,left,right)
  {String.eq(left_key(left),right_key(value)) == False{} : Bool}
def rejected_source_positions_have_nonmatching_keys(left_key,right_key,left,right,index,value,present,rejected):
  match right index rejected:
    case Nil{} index Unit{}:
      L.ex_false({String.eq(left_key(left),right_key(value)) == False{} : Bool},F.none_negative_some(D.Value,value,present))
    case Con{+r,+tail} 0n Both{head,rest}:
      %Selection.equal_present_values_have_equal_payloads(r,value,present) : {String.eq(left_key(left),right_key(_)) == False{} : Bool}
      head
    case Con{+r,+tail} 1n+previous Both{head,rest}: rejected_source_positions_have_nonmatching_keys(~left_key,~right_key,left,tail,previous,value,present,rest)
