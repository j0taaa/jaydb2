# Independent last-occurrence measure with exact indexed witness and greatest
# matching-position proof. This scans source values and never invokes group.
import Base
import ./SequencePaginationProofs.bend as Position
import ./SequenceFilterProofs.bend as Values
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../proof/Foundations.bend as F

def step(tail: Maybe<&2,Nat>,head_matches: Bool) -> Maybe<&2,Nat>:
  match tail:
    case Some{position}: Some{1n+position}
    case None{}: Bool.pick(Maybe<&2,Nat>,head_matches,Some{0n},None{})

def last(~key: D.Value -> String,+wanted: String,xs: List<&2,D.Value>) -> Maybe<&2,Nat>:
  match xs:
    case Nil{}: None{}
    case Con{+x,tail}: step(last(~key,wanted,tail),String.eq(wanted,key(x)))

def Maximal(~key: D.Value -> String,+wanted: String,+xs: List<&2,D.Value>,+position: Nat) -> Type:
  Exists(D.Value,value => L.E<{Position.at(xs,position) == Some{value} : Maybe<&2,D.Value>},
    L.E<{String.eq(wanted,key(value)) == True{} : Bool},
      @+index: Nat -> @+other: D.Value -> {Position.at(xs,index) == Some{other} : Maybe<&2,D.Value>} -> {String.eq(wanted,key(other)) == True{} : Bool} -> {Nat.is_le(index,position) == True{} : Bool}>>)

def Correct(~key: D.Value -> String,+wanted: String,+xs: List<&2,D.Value>,result: Maybe<&2,Nat>) -> Type:
  match result:
    case Some{position}: Maximal(~key,wanted,xs,position)
    case None{}: @+index: Nat -> @+value: D.Value -> {Position.at(xs,index) == Some{value} : Maybe<&2,D.Value>} -> {String.eq(wanted,key(value)) == False{} : Bool}

def absent_cons_position(~key: D.Value -> String,+wanted: String,+x: D.Value,+tail: List<&2,D.Value>,index: Nat,+value: D.Value,
  present: {Position.at(Con{x,tail},index) == Some{value} : Maybe<&2,D.Value>},head_absent: {String.eq(wanted,key(x)) == False{} : Bool},
  absent_tail: @+index: Nat -> @+value: D.Value -> {Position.at(tail,index) == Some{value} : Maybe<&2,D.Value>} -> {String.eq(wanted,key(value)) == False{} : Bool}) -> {String.eq(wanted,key(value)) == False{} : Bool}:
  match index:
    case 0n:
      Equal.trans(Bool,String.eq(wanted,key(value)),String.eq(wanted,key(x)),False{},Equal.cong(D.Value,Bool,item => String.eq(wanted,key(item)),value,x,Equal.sym(D.Value,x,value,Values.equal_present_values_have_equal_payloads(x,value,present))),head_absent)
    case 1n+previous: absent_tail(previous,value,present)

def lifted_bound(~key: D.Value -> String,+wanted: String,+x: D.Value,+tail: List<&2,D.Value>,+position: Nat,index: Nat,+other: D.Value,
  present: {Position.at(Con{x,tail},index) == Some{other} : Maybe<&2,D.Value>},matched: {String.eq(wanted,key(other)) == True{} : Bool},
  maximal: @+index: Nat -> @+value: D.Value -> {Position.at(tail,index) == Some{value} : Maybe<&2,D.Value>} -> {String.eq(wanted,key(value)) == True{} : Bool} -> {Nat.is_le(index,position) == True{} : Bool}) -> {Nat.is_le(index,1n+position) == True{} : Bool}:
  match index:
    case 0n: {==}
    case 1n+previous: maximal(previous,other,present,matched)

def maximal_lifts_through_a_source_cons(~key: D.Value -> String,+wanted: String,+x: D.Value,+tail: List<&2,D.Value>,+position: Nat,maximal: Maximal(~key,wanted,tail,position)) -> Maximal(~key,wanted,Con{x,tail},1n+position):
  match maximal:
    case Tuple{+value,L.Both{at,L.Both{matched,greatest}}}:
      Tuple{value,L.Both{at,L.Both{matched,+index => +other => present => matching => lifted_bound(~key,wanted,x,tail,position,index,other,present,matching,greatest)}}}

def first_position_bound(~key: D.Value -> String,+wanted: String,+x: D.Value,+tail: List<&2,D.Value>,index: Nat,+other: D.Value,
  present: {Position.at(Con{x,tail},index) == Some{other} : Maybe<&2,D.Value>},matched: {String.eq(wanted,key(other)) == True{} : Bool},
  absent_tail: @+index: Nat -> @+value: D.Value -> {Position.at(tail,index) == Some{value} : Maybe<&2,D.Value>} -> {String.eq(wanted,key(value)) == False{} : Bool}) -> {Nat.is_le(index,0n) == True{} : Bool}:
  match index:
    case 0n: {==}
    case 1n+previous:
      F.absurd_boolean({False{} == True{} : Bool},Equal.trans(Bool,False{},String.eq(wanted,key(other)),True{},Equal.sym(Bool,String.eq(wanted,key(other)),False{},absent_tail(previous,other,present)),matched))

def empty_tail_choice(~key: D.Value -> String,matched: Bool,+wanted: String,+x: D.Value,+tail: List<&2,D.Value>,actual: {String.eq(wanted,key(x)) == matched : Bool},
  absent_tail: @+index: Nat -> @+value: D.Value -> {Position.at(tail,index) == Some{value} : Maybe<&2,D.Value>} -> {String.eq(wanted,key(value)) == False{} : Bool}) -> Correct(~key,wanted,Con{x,tail},step(None{},matched)):
  match matched:
    case False{}: +index => +value => present => absent_cons_position(~key,wanted,x,tail,index,value,present,actual,absent_tail)
    case True{}: Tuple{x,L.Both{{==},L.Both{actual,+index => +other => present => matching => first_position_bound(~key,wanted,x,tail,index,other,present,matching,absent_tail)}}}

def result_case(~key: D.Value -> String,+wanted: String,+x: D.Value,+tail: List<&2,D.Value>,result: Maybe<&2,Nat>,correct: Correct(~key,wanted,tail,result)) -> Correct(~key,wanted,Con{x,tail},step(result,String.eq(wanted,key(x)))):
  match result:
    case Some{+position}: maximal_lifts_through_a_source_cons(~key,wanted,x,tail,position,correct)
    case None{}: empty_tail_choice(~key,String.eq(wanted,key(x)),wanted,x,tail,{==},correct)

law last_is_exactly_the_greatest_original_matching_position:
  for ~key: D.Value -> String
  for +wanted: String
  for +xs: List<&2,D.Value>
  Correct(~key,wanted,xs,last(~key,wanted,xs))
def last_is_exactly_the_greatest_original_matching_position(key,wanted,xs):
  match xs:
    case Nil{}: +index => +value => present => L.ex_false({String.eq(wanted,key(value)) == False{} : Bool},F.none_negative_some(D.Value,value,present))
    case Con{+x,+tail}: result_case(~key,wanted,x,tail,last(~key,wanted,tail),last_is_exactly_the_greatest_original_matching_position(~key,wanted,tail))
