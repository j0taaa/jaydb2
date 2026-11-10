# Explicit environment predicate selection and independent indexed meaning.
# The environment is ordinary DATA, never captured by a static template.
# This proof-only source comprehension is independent of Sequence.group.
import Base
import ./SequencePaginationProofs.bend as Position
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ./Sequence.bend as Sequence
import ../proof/Foundations.bend as F

def select(~keep: String -> D.Value -> Bool,+environment: String,xs: List<&2,D.Value>) -> List<&2,D.Value>:
  match xs:
    case Nil{}: Nil{}
    case Con{+x,tail}: Sequence.include(keep(environment,x),x,select(~keep,environment,tail))

def tick(kept: Bool,count: Nat) -> Nat:
  match kept:
    case False{}: count
    case True{}: 1n+count

def matches(~keep: String -> D.Value -> Bool,+environment: String,xs: List<&2,D.Value>) -> Nat:
  match xs:
    case Nil{}: 0n
    case Con{+x,tail}: tick(keep(environment,x),matches(~keep,environment,tail))

def before(~keep: String -> D.Value -> Bool,+environment: String,xs: List<&2,D.Value>,index: Nat) -> Nat:
  match xs:
    case Nil{}: 0n
    case Con{+x,tail}:
      match index:
        case 0n: 0n
        case 1n+previous: tick(keep(environment,x),before(~keep,environment,tail,previous))

def Origin(~keep: String -> D.Value -> Bool,+environment: String,+xs: List<&2,D.Value>,+rank: Nat,+value: D.Value) -> Type:
  Exists(Nat,position => L.E<{Position.at(xs,position) == Some{value} : Maybe<&2,D.Value>},
    L.E<{keep(environment,value) == True{} : Bool},{before(~keep,environment,xs,position) == rank : Nat}>>)

law equal_present_values_have_equal_payloads:
  for +x: D.Value
  for +y: D.Value
  for same: {Some{x} == Some{y} : Maybe<&2,D.Value>}
  {x == y : D.Value}
def equal_present_values_have_equal_payloads(x,y,same):
  Equal.cong(Maybe<&2,D.Value>,D.Value,result => F.extract_or(D.Value,result,D.VAbsent{}),Some{x},Some{y},same)

def present_value_inherits_the_head_predicate(~keep: String -> D.Value -> Bool,+environment: String,+x: D.Value,+value: D.Value,
  same: {Some{x} == Some{value} : Maybe<&2,D.Value>},kept: {keep(environment,value) == True{} : Bool}) -> {keep(environment,x) == True{} : Bool}:
  Equal.trans(Bool,keep(environment,x),keep(environment,value),True{},Equal.cong(D.Value,Bool,item => keep(environment,item),x,value,equal_present_values_have_equal_payloads(x,value,same)),kept)

def include_length(kept: Bool,+x: D.Value,+tail: List<&2,D.Value>,+count: Nat,correct: {Sequence.length(tail) == count : Nat}) ->
  {Sequence.length(Sequence.include(kept,x,tail)) == tick(kept,count) : Nat}:
  match kept:
    case False{}: correct
    case True{}: Equal.cong(Nat,Nat,n => 1n+n,Sequence.length(tail),count,correct)

law filter_length_is_exactly_the_number_of_matching_occurrences:
  for ~keep: String -> D.Value -> Bool
  for +environment: String
  for +xs: List<&2,D.Value>
  {Sequence.length(select(~keep,environment,xs)) == matches(~keep,environment,xs) : Nat}
def filter_length_is_exactly_the_number_of_matching_occurrences(keep,environment,xs):
  match xs:
    case Nil{}: {==}
    case Con{+x,+tail}: include_length(keep(environment,x),x,select(~keep,environment,tail),matches(~keep,environment,tail),filter_length_is_exactly_the_number_of_matching_occurrences(~keep,environment,tail))

def lift_tail_origin(~keep: String -> D.Value -> Bool,+environment: String,+kept: Bool,+x: D.Value,+tail: List<&2,D.Value>,+rank: Nat,+value: D.Value,
  actual: {keep(environment,x) == kept : Bool},origin: Origin(~keep,environment,tail,rank,value)) -> Origin(~keep,environment,Con{x,tail},tick(kept,rank),value):
  match origin:
    case Tuple{+position,L.Both{at,L.Both{predicate,ranked}}}:
      Tuple{1n+position,L.Both{at,L.Both{predicate,
        Equal.trans(Nat,before(~keep,environment,Con{x,tail},1n+position),tick(kept,before(~keep,environment,tail,position)),tick(kept,rank),
          Equal.cong(Bool,Nat,choice => tick(choice,before(~keep,environment,tail,position)),keep(environment,x),kept,actual),Equal.cong(Nat,Nat,n => tick(kept,n),before(~keep,environment,tail,position),rank,ranked))}}}

def output_origin_case(~keep: String -> D.Value -> Bool,+environment: String,kept: Bool,+x: D.Value,+tail: List<&2,D.Value>,+rank: Nat,+value: D.Value,
  +actual: {keep(environment,x) == kept : Bool},+present: {Position.at(Sequence.include(kept,x,select(~keep,environment,tail)),rank) == Some{value} : Maybe<&2,D.Value>},
  recursive: @rank: Nat -> @value: D.Value -> {Position.at(select(~keep,environment,tail),rank) == Some{value} : Maybe<&2,D.Value>} -> Origin(~keep,environment,tail,rank,value)) -> Origin(~keep,environment,Con{x,tail},rank,value):
  match kept rank:
    case True{} 0n:
      Tuple{0n,L.Both{present,L.Both{Equal.trans(Bool,keep(environment,value),keep(environment,x),True{},Equal.cong(D.Value,Bool,item => keep(environment,item),value,x,Equal.sym(D.Value,x,value,equal_present_values_have_equal_payloads(x,value,present))),actual),{==}}}}
    case True{} 1n+previous: lift_tail_origin(~keep,environment,True{},x,tail,previous,value,actual,recursive(previous,value,present))
    case False{} rank: lift_tail_origin(~keep,environment,False{},x,tail,rank,value,actual,recursive(rank,value,present))

law every_filtered_output_has_its_exact_matching_source_position_and_rank:
  for ~keep: String -> D.Value -> Bool
  for +environment: String
  for +xs: List<&2,D.Value>
  for +rank: Nat
  for +value: D.Value
  for present: {Position.at(select(~keep,environment,xs),rank) == Some{value} : Maybe<&2,D.Value>}
  Origin(~keep,environment,xs,rank,value)
def every_filtered_output_has_its_exact_matching_source_position_and_rank(keep,environment,xs,rank,value,present):
  match xs:
    case Nil{}: L.ex_false(Origin(~keep,environment,Nil{},rank,value),F.none_negative_some(D.Value,value,present))
    case Con{+x,+tail}: output_origin_case(~keep,environment,keep(environment,x),x,tail,rank,value,{==},present,+i => +v => evidence => every_filtered_output_has_its_exact_matching_source_position_and_rank(~keep,environment,tail,i,v,evidence))

def include_preserves_tail_rank(kept: Bool,+x: D.Value,+tail: List<&2,D.Value>,+rank: Nat,+value: D.Value,
  present: {Position.at(tail,rank) == Some{value} : Maybe<&2,D.Value>}) ->
  {Position.at(Sequence.include(kept,x,tail),tick(kept,rank)) == Some{value} : Maybe<&2,D.Value>}:
  match kept:
    case True{}: present
    case False{}: present

def kept_head_is_at_output_zero(~keep: String -> D.Value -> Bool,+environment: String,+x: D.Value,+tail: List<&2,D.Value>,+value: D.Value,
  +same: {Some{x} == Some{value} : Maybe<&2,D.Value>},kept: {keep(environment,value) == True{} : Bool}) ->
  {Position.at(select(~keep,environment,Con{x,tail}),0n) == Some{value} : Maybe<&2,D.Value>}:
  Equal.trans(Maybe<&2,D.Value>,Position.at(Sequence.include(keep(environment,x),x,select(~keep,environment,tail)),0n),Some{x},Some{value},
    Equal.cong(Bool,Maybe<&2,D.Value>,choice => Position.at(Sequence.include(choice,x,select(~keep,environment,tail)),0n),keep(environment,x),True{},present_value_inherits_the_head_predicate(~keep,environment,x,value,same,kept)),same)

law every_matching_source_occurrence_is_retained_at_its_exact_rank:
  for ~keep: String -> D.Value -> Bool
  for +environment: String
  for +xs: List<&2,D.Value>
  for +position: Nat
  for +value: D.Value
  for present: {Position.at(xs,position) == Some{value} : Maybe<&2,D.Value>}
  for kept: {keep(environment,value) == True{} : Bool}
  {Position.at(select(~keep,environment,xs),before(~keep,environment,xs,position)) == Some{value} : Maybe<&2,D.Value>}
def every_matching_source_occurrence_is_retained_at_its_exact_rank(keep,environment,xs,position,value,present,kept):
  match xs:
    case Nil{}: L.ex_false({Position.at(select(~keep,environment,Nil{}),before(~keep,environment,Nil{},position)) == Some{value} : Maybe<&2,D.Value>},F.none_negative_some(D.Value,value,present))
    case Con{+x,+tail}:
      match position:
        case 0n: kept_head_is_at_output_zero(~keep,environment,x,tail,value,present,kept)
        case 1n+previous: include_preserves_tail_rank(keep(environment,x),x,select(~keep,environment,tail),before(~keep,environment,tail,previous),value,every_matching_source_occurrence_is_retained_at_its_exact_rank(~keep,environment,tail,previous,value,present,kept))

law ticking_both_counts_preserves_their_strict_order:
  for +kept: Bool
  for +a: Nat
  for +b: Nat
  {Nat.is_lt(tick(kept,a),tick(kept,b)) == Nat.is_lt(a,b) : Bool}
def ticking_both_counts_preserves_their_strict_order(kept,a,b):
  match kept:
    case True{}: {==}
    case False{}: {==}

# This explicit order theorem connects the rank witnesses above to ordered
# subsequence semantics; distinct matched positions cannot collapse/reverse.
law matching_source_occurrences_preserve_strict_position_order:
  for ~keep: String -> D.Value -> Bool
  for +environment: String
  for +xs: List<&2,D.Value>
  for +first: Nat
  for +later: Nat
  for +value: D.Value
  for present: {Position.at(xs,first) == Some{value} : Maybe<&2,D.Value>}
  for kept: {keep(environment,value) == True{} : Bool}
  for ordered: {Nat.is_lt(first,later) == True{} : Bool}
  {Nat.is_lt(before(~keep,environment,xs,first),before(~keep,environment,xs,later)) == True{} : Bool}
def matching_source_occurrences_preserve_strict_position_order(keep,environment,xs,first,later,value,present,kept,ordered):
  match xs:
    case Nil{}: L.ex_false({Nat.is_lt(0n,0n) == True{} : Bool},F.none_negative_some(D.Value,value,present))
    case Con{+x,+tail}:
      match first later:
        case 0n 0n: F.absurd_boolean({False{} == True{} : Bool},ordered)
        case 0n 1n+after:
          Equal.cong(Bool,Bool,choice => Nat.is_lt(0n,tick(choice,before(~keep,environment,tail,after))),keep(environment,x),True{},present_value_inherits_the_head_predicate(~keep,environment,x,value,present,kept))
        case 1n+previous 0n: F.absurd_boolean({Nat.is_lt(before(~keep,environment,Con{x,tail},1n+previous),0n) == True{} : Bool},ordered)
        case 1n+previous 1n+after:
          Equal.trans(Bool,Nat.is_lt(tick(keep(environment,x),before(~keep,environment,tail,previous)),tick(keep(environment,x),before(~keep,environment,tail,after))),Nat.is_lt(before(~keep,environment,tail,previous),before(~keep,environment,tail,after)),True{},ticking_both_counts_preserves_their_strict_order(keep(environment,x),before(~keep,environment,tail,previous),before(~keep,environment,tail,after)),matching_source_occurrences_preserve_strict_position_order(~keep,environment,tail,previous,after,value,present,kept,ordered))

def Meaning(~keep: String -> D.Value -> Bool,+environment: String,+xs: List<&2,D.Value>,+result: List<&2,D.Value>) -> Type:
  L.E<{Sequence.length(result) == matches(~keep,environment,xs) : Nat},
    L.E<@rank: Nat -> @value: D.Value -> {Position.at(result,rank) == Some{value} : Maybe<&2,D.Value>} -> Origin(~keep,environment,xs,rank,value),
      @position: Nat -> @value: D.Value -> {Position.at(xs,position) == Some{value} : Maybe<&2,D.Value>} -> {keep(environment,value) == True{} : Bool} -> {Position.at(result,before(~keep,environment,xs,position)) == Some{value} : Maybe<&2,D.Value>}>>

law actual_selection_is_exact_complete_and_ordered:
  for ~keep: String -> D.Value -> Bool
  for +environment: String
  for +xs: List<&2,D.Value>
  Meaning(~keep,environment,xs,select(~keep,environment,xs))
def actual_selection_is_exact_complete_and_ordered(keep,environment,xs):
  L.Both{filter_length_is_exactly_the_number_of_matching_occurrences(~keep,environment,xs),L.Both{
    +rank => +value => present => every_filtered_output_has_its_exact_matching_source_position_and_rank(~keep,environment,xs,rank,value,present),
    +position => +value => present => kept => every_matching_source_occurrence_is_retained_at_its_exact_rank(~keep,environment,xs,position,value,present,kept)}}
