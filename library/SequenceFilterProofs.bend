# Independent indexed filter specification. Each output index has a matching
# source occurrence and its exact rank among predicate-true source positions;
# conversely EVERY matching source occurrence appears at that rank. Thus no
# matching duplicate can disappear and no extra value can enter the result.
import Base
import ./SequencePaginationProofs.bend as Position
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ./Sequence.bend as Sequence
import ../proof/Foundations.bend as F

def tick(kept: Bool,count: Nat) -> Nat:
  match kept:
    case False{}: count
    case True{}: 1n+count

def matches(~keep: D.Value -> Bool,xs: List<&2,D.Value>) -> Nat:
  match xs:
    case Nil{}: 0n
    case Con{+x,tail}: tick(keep(x),matches(~keep,tail))

def before(~keep: D.Value -> Bool,xs: List<&2,D.Value>,index: Nat) -> Nat:
  match xs:
    case Nil{}: 0n
    case Con{+x,tail}:
      match index:
        case 0n: 0n
        case 1n+previous: tick(keep(x),before(~keep,tail,previous))

def Origin(~keep: D.Value -> Bool,+xs: List<&2,D.Value>,+rank: Nat,+value: D.Value) -> Type:
  Exists(Nat,position => L.E<{Position.at(xs,position) == Some{value} : Maybe<&2,D.Value>},
    L.E<{keep(value) == True{} : Bool},{before(~keep,xs,position) == rank : Nat}>>)

law equal_present_values_have_equal_payloads:
  for +x: D.Value
  for +y: D.Value
  for same: {Some{x} == Some{y} : Maybe<&2,D.Value>}
  {x == y : D.Value}
def equal_present_values_have_equal_payloads(x,y,same):
  Equal.cong(Maybe<&2,D.Value>,D.Value,result => F.extract_or(D.Value,result,D.VAbsent{}),Some{x},Some{y},same)

def present_value_inherits_the_head_predicate(~keep: D.Value -> Bool,+x: D.Value,+value: D.Value,
  same: {Some{x} == Some{value} : Maybe<&2,D.Value>},kept: {keep(value) == True{} : Bool}) -> {keep(x) == True{} : Bool}:
  Equal.trans(Bool,keep(x),keep(value),True{},Equal.cong(D.Value,Bool,keep,x,value,equal_present_values_have_equal_payloads(x,value,same)),kept)

def include_length(kept: Bool,+x: D.Value,+tail: List<&2,D.Value>,+count: Nat,correct: {Sequence.length(tail) == count : Nat}) ->
  {Sequence.length(Sequence.include(kept,x,tail)) == tick(kept,count) : Nat}:
  match kept:
    case False{}: correct
    case True{}: Equal.cong(Nat,Nat,n => 1n+n,Sequence.length(tail),count,correct)

law filter_length_is_exactly_the_number_of_matching_occurrences:
  for ~keep: D.Value -> Bool
  for +xs: List<&2,D.Value>
  {Sequence.length(Sequence.filter(~keep,xs)) == matches(~keep,xs) : Nat}
def filter_length_is_exactly_the_number_of_matching_occurrences(keep,xs):
  match xs:
    case Nil{}: {==}
    case Con{+x,+tail}: include_length(keep(x),x,Sequence.filter(~keep,tail),matches(~keep,tail),filter_length_is_exactly_the_number_of_matching_occurrences(~keep,tail))

def lift_tail_origin(~keep: D.Value -> Bool,+kept: Bool,+x: D.Value,+tail: List<&2,D.Value>,+rank: Nat,+value: D.Value,
  actual: {keep(x) == kept : Bool},origin: Origin(~keep,tail,rank,value)) -> Origin(~keep,Con{x,tail},tick(kept,rank),value):
  match origin:
    case Tuple{+position,L.Both{at,L.Both{predicate,ranked}}}:
      Tuple{1n+position,L.Both{at,L.Both{predicate,
        Equal.trans(Nat,before(~keep,Con{x,tail},1n+position),tick(kept,before(~keep,tail,position)),tick(kept,rank),
          Equal.cong(Bool,Nat,choice => tick(choice,before(~keep,tail,position)),keep(x),kept,actual),Equal.cong(Nat,Nat,n => tick(kept,n),before(~keep,tail,position),rank,ranked))}}}

def output_origin_case(~keep: D.Value -> Bool,kept: Bool,+x: D.Value,+tail: List<&2,D.Value>,+rank: Nat,+value: D.Value,
  +actual: {keep(x) == kept : Bool},+present: {Position.at(Sequence.include(kept,x,Sequence.filter(~keep,tail)),rank) == Some{value} : Maybe<&2,D.Value>},
  recursive: @rank: Nat -> @value: D.Value -> {Position.at(Sequence.filter(~keep,tail),rank) == Some{value} : Maybe<&2,D.Value>} -> Origin(~keep,tail,rank,value)) -> Origin(~keep,Con{x,tail},rank,value):
  match kept rank:
    case True{} 0n:
      Tuple{0n,L.Both{present,L.Both{Equal.trans(Bool,keep(value),keep(x),True{},Equal.cong(D.Value,Bool,keep,value,x,Equal.sym(D.Value,x,value,equal_present_values_have_equal_payloads(x,value,present))),actual),{==}}}}
    case True{} 1n+previous: lift_tail_origin(~keep,True{},x,tail,previous,value,actual,recursive(previous,value,present))
    case False{} rank: lift_tail_origin(~keep,False{},x,tail,rank,value,actual,recursive(rank,value,present))

law every_filtered_output_has_its_exact_matching_source_position_and_rank:
  for ~keep: D.Value -> Bool
  for +xs: List<&2,D.Value>
  for +rank: Nat
  for +value: D.Value
  for present: {Position.at(Sequence.filter(~keep,xs),rank) == Some{value} : Maybe<&2,D.Value>}
  Origin(~keep,xs,rank,value)
def every_filtered_output_has_its_exact_matching_source_position_and_rank(keep,xs,rank,value,present):
  match xs:
    case Nil{}: L.ex_false(Origin(~keep,Nil{},rank,value),F.none_negative_some(D.Value,value,present))
    case Con{+x,+tail}: output_origin_case(~keep,keep(x),x,tail,rank,value,{==},present,+i => +v => evidence => every_filtered_output_has_its_exact_matching_source_position_and_rank(~keep,tail,i,v,evidence))

def include_preserves_tail_rank(kept: Bool,+x: D.Value,+tail: List<&2,D.Value>,+rank: Nat,+value: D.Value,
  present: {Position.at(tail,rank) == Some{value} : Maybe<&2,D.Value>}) ->
  {Position.at(Sequence.include(kept,x,tail),tick(kept,rank)) == Some{value} : Maybe<&2,D.Value>}:
  match kept:
    case True{}: present
    case False{}: present

def kept_head_is_at_output_zero(~keep: D.Value -> Bool,+x: D.Value,+tail: List<&2,D.Value>,+value: D.Value,
  +same: {Some{x} == Some{value} : Maybe<&2,D.Value>},kept: {keep(value) == True{} : Bool}) ->
  {Position.at(Sequence.filter(~keep,Con{x,tail}),0n) == Some{value} : Maybe<&2,D.Value>}:
  Equal.trans(Maybe<&2,D.Value>,Position.at(Sequence.include(keep(x),x,Sequence.filter(~keep,tail)),0n),Some{x},Some{value},
    Equal.cong(Bool,Maybe<&2,D.Value>,choice => Position.at(Sequence.include(choice,x,Sequence.filter(~keep,tail)),0n),keep(x),True{},present_value_inherits_the_head_predicate(~keep,x,value,same,kept)),same)

law every_matching_source_occurrence_is_retained_at_its_exact_rank:
  for ~keep: D.Value -> Bool
  for +xs: List<&2,D.Value>
  for +position: Nat
  for +value: D.Value
  for present: {Position.at(xs,position) == Some{value} : Maybe<&2,D.Value>}
  for kept: {keep(value) == True{} : Bool}
  {Position.at(Sequence.filter(~keep,xs),before(~keep,xs,position)) == Some{value} : Maybe<&2,D.Value>}
def every_matching_source_occurrence_is_retained_at_its_exact_rank(keep,xs,position,value,present,kept):
  match xs:
    case Nil{}: L.ex_false({Position.at(Sequence.filter(~keep,Nil{}),before(~keep,Nil{},position)) == Some{value} : Maybe<&2,D.Value>},F.none_negative_some(D.Value,value,present))
    case Con{+x,+tail}:
      match position:
        case 0n: kept_head_is_at_output_zero(~keep,x,tail,value,present,kept)
        case 1n+previous: include_preserves_tail_rank(keep(x),x,Sequence.filter(~keep,tail),before(~keep,tail,previous),value,every_matching_source_occurrence_is_retained_at_its_exact_rank(~keep,tail,previous,value,present,kept))

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
  for ~keep: D.Value -> Bool
  for +xs: List<&2,D.Value>
  for +first: Nat
  for +later: Nat
  for +value: D.Value
  for present: {Position.at(xs,first) == Some{value} : Maybe<&2,D.Value>}
  for kept: {keep(value) == True{} : Bool}
  for ordered: {Nat.is_lt(first,later) == True{} : Bool}
  {Nat.is_lt(before(~keep,xs,first),before(~keep,xs,later)) == True{} : Bool}
def matching_source_occurrences_preserve_strict_position_order(keep,xs,first,later,value,present,kept,ordered):
  match xs:
    case Nil{}: L.ex_false({Nat.is_lt(0n,0n) == True{} : Bool},F.none_negative_some(D.Value,value,present))
    case Con{+x,+tail}:
      match first later:
        case 0n 0n: F.absurd_boolean({False{} == True{} : Bool},ordered)
        case 0n 1n+after:
          Equal.cong(Bool,Bool,choice => Nat.is_lt(0n,tick(choice,before(~keep,tail,after))),keep(x),True{},present_value_inherits_the_head_predicate(~keep,x,value,present,kept))
        case 1n+previous 0n: F.absurd_boolean({Nat.is_lt(before(~keep,Con{x,tail},1n+previous),0n) == True{} : Bool},ordered)
        case 1n+previous 1n+after:
          Equal.trans(Bool,Nat.is_lt(tick(keep(x),before(~keep,tail,previous)),tick(keep(x),before(~keep,tail,after))),Nat.is_lt(before(~keep,tail,previous),before(~keep,tail,after)),True{},ticking_both_counts_preserves_their_strict_order(keep(x),before(~keep,tail,previous),before(~keep,tail,after)),matching_source_occurrences_preserve_strict_position_order(~keep,tail,previous,after,value,present,kept,ordered))

def Meaning(~keep: D.Value -> Bool,+xs: List<&2,D.Value>,+result: List<&2,D.Value>) -> Type:
  L.E<{Sequence.length(result) == matches(~keep,xs) : Nat},
    L.E<@rank: Nat -> @value: D.Value -> {Position.at(result,rank) == Some{value} : Maybe<&2,D.Value>} -> Origin(~keep,xs,rank,value),
      @position: Nat -> @value: D.Value -> {Position.at(xs,position) == Some{value} : Maybe<&2,D.Value>} -> {keep(value) == True{} : Bool} -> {Position.at(result,before(~keep,xs,position)) == Some{value} : Maybe<&2,D.Value>}>>

law actual_filter_is_exact_complete_and_ordered_selection:
  for ~keep: D.Value -> Bool
  for +xs: List<&2,D.Value>
  Meaning(~keep,xs,Sequence.filter(~keep,xs))
def actual_filter_is_exact_complete_and_ordered_selection(keep,xs):
  L.Both{filter_length_is_exactly_the_number_of_matching_occurrences(~keep,xs),L.Both{
    +rank => +value => present => every_filtered_output_has_its_exact_matching_source_position_and_rank(~keep,xs,rank,value,present),
    +position => +value => present => kept => every_matching_source_occurrence_is_retained_at_its_exact_rank(~keep,xs,position,value,present,kept)}}
