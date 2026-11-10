# A row's independent specification uses original right-hand source positions,
# matching-prefix ranks, and exact encoded payloads. The only mapping below
# encodes an ALREADY selected list; it is not another join implementation.
import Base
import ./SequencePaginationProofs.bend as Position
import ./SequenceSelectionProofs.bend as Selection
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ./Relation.bend as Relation
import ./Sequence.bend as Sequence
import ../proof/Foundations.bend as F


def pair(left: D.Value,right: D.Value) -> D.Value:
  D.VList{left,D.VList{right,D.VListEmpty{}}}

def selected(~right_key: D.Value -> String,wanted: String,value: D.Value) -> Bool:
  String.eq(wanted,right_key(value))

def encode(+left: D.Value,right: List<&2,D.Value>) -> List<&2,D.Value>:
  match right:
    case Nil{}: Nil{}
    case Con{r,tail}: Con{pair(left,r),encode(left,tail)}

def encoded_at(left: D.Value,value: Maybe<&2,D.Value>) -> Maybe<&2,D.Value>:
  match value:
    case None{}: None{}
    case Some{right}: Some{pair(left,right)}

def encode_include(kept: Bool,+left: D.Value,+right: D.Value,+tail: List<&2,D.Value>) ->
  {Relation.include(kept,left,right,encode(left,tail)) == encode(left,Sequence.include(kept,right,tail)) : List<&2,D.Value>}:
  match kept:
    case True{}: {==}
    case False{}: {==}

law actual_matches_are_exact_encodings_of_selected_right_occurrences:
  for ~left_key: D.Value -> String
  for ~right_key: D.Value -> String
  for +left: D.Value
  for +right: List<&2,D.Value>
  {Relation.matches(~left_key,~right_key,left,right) == encode(left,Selection.select(~selected(~right_key),left_key(left),right)) : List<&2,D.Value>}
def actual_matches_are_exact_encodings_of_selected_right_occurrences(left_key,right_key,left,right):
  match right:
    case Nil{}: {==}
    case Con{+r,+tail}:
      Equal.trans(List<&2,D.Value>,Relation.matches(~left_key,~right_key,left,Con{r,tail}),Relation.include(String.eq(left_key(left),right_key(r)),left,r,encode(left,Selection.select(~selected(~right_key),left_key(left),tail))),encode(left,Selection.select(~selected(~right_key),left_key(left),Con{r,tail})),
        Equal.cong(List<&2,D.Value>,List<&2,D.Value>,found => Relation.include(String.eq(left_key(left),right_key(r)),left,r,found),Relation.matches(~left_key,~right_key,left,tail),encode(left,Selection.select(~selected(~right_key),left_key(left),tail)),actual_matches_are_exact_encodings_of_selected_right_occurrences(~left_key,~right_key,left,tail)),encode_include(String.eq(left_key(left),right_key(r)),left,r,Selection.select(~selected(~right_key),left_key(left),tail)))

law pair_encoding_preserves_list_length:
  for +left: D.Value
  for +right: List<&2,D.Value>
  {Sequence.length(encode(left,right)) == Sequence.length(right) : Nat}
def pair_encoding_preserves_list_length(left,right):
  match right:
    case Nil{}: {==}
    case Con{r,+tail}: Equal.cong(Nat,Nat,n => 1n+n,Sequence.length(encode(left,tail)),Sequence.length(tail),pair_encoding_preserves_list_length(left,tail))

law pair_encoding_has_exact_indexed_payloads:
  for +left: D.Value
  for +right: List<&2,D.Value>
  for +index: Nat
  {Position.at(encode(left,right),index) == encoded_at(left,Position.at(right,index)) : Maybe<&2,D.Value>}
def pair_encoding_has_exact_indexed_payloads(left,right,index):
  match right:
    case Nil{}: {==}
    case Con{r,+tail}:
      match index:
        case 0n: {==}
        case 1n+previous: pair_encoding_has_exact_indexed_payloads(left,tail,previous)

# A separate source position is retained even when several values or encoded
# pairs are identical; this is what makes duplicate multiplicities exact.
def Origin(~left_key: D.Value -> String,~right_key: D.Value -> String,+left: D.Value,+right: List<&2,D.Value>,+rank: Nat,+payload: D.Value) -> Type:
  Exists(Nat,index => Exists(D.Value,value => L.E<{Position.at(right,index) == Some{value} : Maybe<&2,D.Value>},
    L.E<{String.eq(left_key(left),right_key(value)) == True{} : Bool},
      L.E<{Selection.before(~selected(~right_key),left_key(left),right,index) == rank : Nat},{payload == pair(left,value) : D.Value}>>>))


def selected_presence(+left: D.Value,result: Maybe<&2,D.Value>,+payload: D.Value,present: {encoded_at(left,result) == Some{payload} : Maybe<&2,D.Value>}) ->
  Exists(D.Value,value => L.E<{result == Some{value} : Maybe<&2,D.Value>},{payload == pair(left,value) : D.Value}>):
  match result:
    case None{}: L.ex_false(Exists(D.Value,value => L.E<{None{} == Some{value} : Maybe<&2,D.Value>},{payload == pair(left,value) : D.Value}>),F.none_negative_some(D.Value,payload,present))
    case Some{+value}: Tuple{value,L.Both{{==},Equal.sym(D.Value,pair(left,value),payload,Selection.equal_present_values_have_equal_payloads(pair(left,value),payload,present))}}

def repackage_selected_origin(~left_key: D.Value -> String,~right_key: D.Value -> String,+left: D.Value,+right: List<&2,D.Value>,+rank: Nat,+payload: D.Value,+value: D.Value,exact: {payload == pair(left,value) : D.Value},origin: Selection.Origin(~selected(~right_key),left_key(left),right,rank,value)) -> Origin(~left_key,~right_key,left,right,rank,payload):
  match origin:
    case Tuple{index,L.Both{present,L.Both{matched,ranked}}}: Tuple{index,Tuple{value,L.Both{present,L.Both{matched,L.Both{ranked,exact}}}}}

def origin_from_selected_occurrence(~left_key: D.Value -> String,~right_key: D.Value -> String,+left: D.Value,+right: List<&2,D.Value>,+rank: Nat,+payload: D.Value,
  occurrence: Exists(D.Value,value => L.E<{Position.at(Selection.select(~selected(~right_key),left_key(left),right),rank) == Some{value} : Maybe<&2,D.Value>},{payload == pair(left,value) : D.Value}>)) -> Origin(~left_key,~right_key,left,right,rank,payload):
  match occurrence:
    case Tuple{+value,L.Both{present,exact}}:
      repackage_selected_origin(~left_key,~right_key,left,right,rank,payload,value,exact,Selection.every_filtered_output_has_its_exact_matching_source_position_and_rank(~selected(~right_key),left_key(left),right,rank,value,present))

law every_match_output_has_an_exact_matching_right_source_occurrence:
  for ~left_key: D.Value -> String
  for ~right_key: D.Value -> String
  for +left: D.Value
  for +right: List<&2,D.Value>
  for +rank: Nat
  for +payload: D.Value
  for present: {Position.at(Relation.matches(~left_key,~right_key,left,right),rank) == Some{payload} : Maybe<&2,D.Value>}
  Origin(~left_key,~right_key,left,right,rank,payload)
def every_match_output_has_an_exact_matching_right_source_occurrence(left_key,right_key,left,right,rank,payload,present):
  origin_from_selected_occurrence(~left_key,~right_key,left,right,rank,payload,selected_presence(left,Position.at(Selection.select(~selected(~right_key),left_key(left),right),rank),payload,
    Equal.trans(Maybe<&2,D.Value>,encoded_at(left,Position.at(Selection.select(~selected(~right_key),left_key(left),right),rank)),Position.at(encode(left,Selection.select(~selected(~right_key),left_key(left),right)),rank),Some{payload},
      Equal.sym(Maybe<&2,D.Value>,Position.at(encode(left,Selection.select(~selected(~right_key),left_key(left),right)),rank),encoded_at(left,Position.at(Selection.select(~selected(~right_key),left_key(left),right),rank)),pair_encoding_has_exact_indexed_payloads(left,Selection.select(~selected(~right_key),left_key(left),right),rank)),
      Equal.trans(Maybe<&2,D.Value>,Position.at(encode(left,Selection.select(~selected(~right_key),left_key(left),right)),rank),Position.at(Relation.matches(~left_key,~right_key,left,right),rank),Some{payload},
        Equal.cong(List<&2,D.Value>,Maybe<&2,D.Value>,items => Position.at(items,rank),encode(left,Selection.select(~selected(~right_key),left_key(left),right)),Relation.matches(~left_key,~right_key,left,right),Equal.sym(List<&2,D.Value>,Relation.matches(~left_key,~right_key,left,right),encode(left,Selection.select(~selected(~right_key),left_key(left),right)),actual_matches_are_exact_encodings_of_selected_right_occurrences(~left_key,~right_key,left,right))),present))))

law every_matching_right_source_occurrence_is_encoded_at_its_exact_rank:
  for ~left_key: D.Value -> String
  for ~right_key: D.Value -> String
  for +left: D.Value
  for +right: List<&2,D.Value>
  for +index: Nat
  for +value: D.Value
  for present: {Position.at(right,index) == Some{value} : Maybe<&2,D.Value>}
  for matched: {String.eq(left_key(left),right_key(value)) == True{} : Bool}
  {Position.at(Relation.matches(~left_key,~right_key,left,right),Selection.before(~selected(~right_key),left_key(left),right,index)) == Some{pair(left,value)} : Maybe<&2,D.Value>}
def every_matching_right_source_occurrence_is_encoded_at_its_exact_rank(left_key,right_key,left,right,index,value,present,matched):
  Equal.trans(Maybe<&2,D.Value>,Position.at(Relation.matches(~left_key,~right_key,left,right),Selection.before(~selected(~right_key),left_key(left),right,index)),Position.at(encode(left,Selection.select(~selected(~right_key),left_key(left),right)),Selection.before(~selected(~right_key),left_key(left),right,index)),Some{pair(left,value)},
    Equal.cong(List<&2,D.Value>,Maybe<&2,D.Value>,items => Position.at(items,Selection.before(~selected(~right_key),left_key(left),right,index)),Relation.matches(~left_key,~right_key,left,right),encode(left,Selection.select(~selected(~right_key),left_key(left),right)),actual_matches_are_exact_encodings_of_selected_right_occurrences(~left_key,~right_key,left,right)),
    Equal.trans(Maybe<&2,D.Value>,Position.at(encode(left,Selection.select(~selected(~right_key),left_key(left),right)),Selection.before(~selected(~right_key),left_key(left),right,index)),encoded_at(left,Position.at(Selection.select(~selected(~right_key),left_key(left),right),Selection.before(~selected(~right_key),left_key(left),right,index))),Some{pair(left,value)},
      pair_encoding_has_exact_indexed_payloads(left,Selection.select(~selected(~right_key),left_key(left),right),Selection.before(~selected(~right_key),left_key(left),right,index)),
      Equal.cong(Maybe<&2,D.Value>,Maybe<&2,D.Value>,item => encoded_at(left,item),Position.at(Selection.select(~selected(~right_key),left_key(left),right),Selection.before(~selected(~right_key),left_key(left),right,index)),Some{value},Selection.every_matching_source_occurrence_is_retained_at_its_exact_rank(~selected(~right_key),left_key(left),right,index,value,present,matched))))

def count(~left_key: D.Value -> String,~right_key: D.Value -> String,+left: D.Value,right: List<&2,D.Value>) -> Nat:
  Selection.matches(~selected(~right_key),left_key(left),right)

law matching_row_length_is_exactly_the_number_of_matching_right_occurrences:
  for ~left_key: D.Value -> String
  for ~right_key: D.Value -> String
  for +left: D.Value
  for +right: List<&2,D.Value>
  {Sequence.length(Relation.matches(~left_key,~right_key,left,right)) == count(~left_key,~right_key,left,right) : Nat}
def matching_row_length_is_exactly_the_number_of_matching_right_occurrences(left_key,right_key,left,right):
  Equal.trans(Nat,Sequence.length(Relation.matches(~left_key,~right_key,left,right)),Sequence.length(encode(left,Selection.select(~selected(~right_key),left_key(left),right))),count(~left_key,~right_key,left,right),
    Equal.cong(List<&2,D.Value>,Nat,Sequence.length,Relation.matches(~left_key,~right_key,left,right),encode(left,Selection.select(~selected(~right_key),left_key(left),right)),actual_matches_are_exact_encodings_of_selected_right_occurrences(~left_key,~right_key,left,right)),
    Equal.trans(Nat,Sequence.length(encode(left,Selection.select(~selected(~right_key),left_key(left),right))),Sequence.length(Selection.select(~selected(~right_key),left_key(left),right)),count(~left_key,~right_key,left,right),pair_encoding_preserves_list_length(left,Selection.select(~selected(~right_key),left_key(left),right)),Selection.filter_length_is_exactly_the_number_of_matching_occurrences(~selected(~right_key),left_key(left),right)))

law matching_right_source_positions_preserve_strict_output_order:
  for ~left_key: D.Value -> String
  for ~right_key: D.Value -> String
  for +left: D.Value
  for +right: List<&2,D.Value>
  for +first: Nat
  for +later: Nat
  for +value: D.Value
  for present: {Position.at(right,first) == Some{value} : Maybe<&2,D.Value>}
  for matched: {String.eq(left_key(left),right_key(value)) == True{} : Bool}
  for ordered: {Nat.is_lt(first,later) == True{} : Bool}
  {Nat.is_lt(Selection.before(~selected(~right_key),left_key(left),right,first),Selection.before(~selected(~right_key),left_key(left),right,later)) == True{} : Bool}
def matching_right_source_positions_preserve_strict_output_order(left_key,right_key,left,right,first,later,value,present,matched,ordered):
  Selection.matching_source_occurrences_preserve_strict_position_order(~selected(~right_key),left_key(left),right,first,later,value,present,matched,ordered)

# Full row statement: arbitrary keys and source values only. All observed
# positions below are universally quantified facts INSIDE the specification.
def Meaning(~left_key: D.Value -> String,~right_key: D.Value -> String,+left: D.Value,+right: List<&2,D.Value>,+result: List<&2,D.Value>) -> Type:
  L.E<{Sequence.length(result) == count(~left_key,~right_key,left,right) : Nat},
    L.E<@+rank: Nat -> @+payload: D.Value -> {Position.at(result,rank) == Some{payload} : Maybe<&2,D.Value>} -> Origin(~left_key,~right_key,left,right,rank,payload),
      @+index: Nat -> @+value: D.Value -> {Position.at(right,index) == Some{value} : Maybe<&2,D.Value>} -> {String.eq(left_key(left),right_key(value)) == True{} : Bool} -> {Position.at(result,Selection.before(~selected(~right_key),left_key(left),right,index)) == Some{pair(left,value)} : Maybe<&2,D.Value>}>>

law actual_matching_row_has_exact_occurrences_payloads_multiplicity_and_order:
  for ~left_key: D.Value -> String
  for ~right_key: D.Value -> String
  for +left: D.Value
  for +right: List<&2,D.Value>
  Meaning(~left_key,~right_key,left,right,Relation.matches(~left_key,~right_key,left,right))
def actual_matching_row_has_exact_occurrences_payloads_multiplicity_and_order(left_key,right_key,left,right):
  L.Both{matching_row_length_is_exactly_the_number_of_matching_right_occurrences(~left_key,~right_key,left,right),L.Both{
    +rank => +payload => present => every_match_output_has_an_exact_matching_right_source_occurrence(~left_key,~right_key,left,right,rank,payload,present),
    +index => +value => present => matched => every_matching_right_source_occurrence_is_encoded_at_its_exact_rank(~left_key,~right_key,left,right,index,value,present,matched)}}
