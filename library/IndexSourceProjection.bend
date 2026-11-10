# Independent INDEXED contents of the source projection: exact original
# positions/payloads, complete retention, multiplicity, ranks and strict order.
# Encoded-string comparison is reflected to literal parts equality here.
import Base
import ./IndexSourceRows.bend as Source
import ./IndexSourceContent.bend as Content
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ./Key.bend as Key
import ./Sequence.bend as Sequence
import ./SequencePaginationProofs.bend as Position
import ../proof/Foundations.bend as F
import ../proof/Orders.bend as O

def advance(kept: Bool,rank: Nat) -> Nat:
  match kept:
    case False{}: rank
    case True{}: 1n+rank

def before(entries: List<&2,Source.SourceEntry>,position: Nat,+query: String) -> Nat:
  match entries position:
    case Nil{} position: 0n
    case Con{head,tail} 0n: 0n
    case Con{+head,tail} 1n+previous: advance(Content.matches(query,head),before(tail,previous,query))

type Origin<-query: List<&2,String>,-entries: List<&2,Source.SourceEntry>,-rank: Nat,-value: D.Value> is Data:
  SourceOrigin{position: Nat,entry: Source.SourceEntry,present: {Source.at(entries,position) == Some{entry} : Maybe<&2,Source.SourceEntry>},parts: {query == Source.parts(entry) : List<&2,String>},ranked: {before(entries,position,Key.encode(query)) == rank : Nat},payload: {D.VText{Source.target(entry)} == value : D.Value}}

def literal_match_is_true(+query: List<&2,String>,+entry: Source.SourceEntry,same: {query == Source.parts(entry) : List<&2,String>}) -> {Content.matches(Key.encode(query),entry) == True{} : Bool}:
  Equal.trans(Bool,Content.matches(Key.encode(query),entry),String.eq(Key.encode(query),Key.encode(query)),True{},Equal.cong(String,Bool,value => String.eq(Key.encode(query),value),Key.encode(Source.parts(entry)),Key.encode(query),Equal.sym(String,Key.encode(query),Key.encode(Source.parts(entry)),Equal.cong(List<&2,String>,String,Key.encode,query,Source.parts(entry),same))),O.string_eq_refl(Key.encode(query)))

def lift_origin(+query: List<&2,String>,+head: Source.SourceEntry,+tail: List<&2,Source.SourceEntry>,+kept: Bool,+rank: Nat,+value: D.Value,actual: {Content.matches(Key.encode(query),head) == kept : Bool},origin: Origin<query,tail,rank,value>) -> Origin<query,Con{head,tail},advance(kept,rank),value>:
  match origin:
    case SourceOrigin{+position,+entry,present,parts,ranked,payload}:
      SourceOrigin{1n+position,entry,present,parts,Equal.trans(Nat,before(Con{head,tail},1n+position,Key.encode(query)),advance(kept,before(tail,position,Key.encode(query))),advance(kept,rank),Equal.cong(Bool,Nat,b => advance(b,before(tail,position,Key.encode(query))),Content.matches(Key.encode(query),head),kept,actual),Equal.cong(Nat,Nat,n => advance(kept,n),before(tail,position,Key.encode(query)),rank,ranked)),payload}

def head_case(+query: List<&2,String>,kept: Bool,+head: Source.SourceEntry,+tail: List<&2,Source.SourceEntry>,+rank: Nat,+value: D.Value,actual: {Content.matches(Key.encode(query),head) == kept : Bool},found: {Position.at(Sequence.include(kept,D.VText{Source.target(head)},Content.targets(tail,Key.encode(query))),rank) == Some{value} : Maybe<&2,D.Value>},recursive: @+r: Nat -> @+v: D.Value -> {Position.at(Content.targets(tail,Key.encode(query)),r) == Some{v} : Maybe<&2,D.Value>} -> Origin<query,tail,r,v>) -> Origin<query,Con{head,tail},rank,value>:
  match kept rank:
    case False{} rank: lift_origin(query,head,tail,False{},rank,value,actual,recursive(rank,value,found))
    case True{} 0n: SourceOrigin{0n,head,{==},Content.literal_parts_case(query,head,True{},actual),{==},F.some_injective(D.Value,D.VText{Source.target(head)},value,found)}
    case True{} 1n+previous: lift_origin(query,head,tail,True{},previous,value,actual,recursive(previous,value,found))

law every_projected_output_has_an_original_matching_parts_source_position_and_exact_rank:
  for +query: List<&2,String>
  for +entries: List<&2,Source.SourceEntry>
  for +rank: Nat
  for +value: D.Value
  for found: {Position.at(Content.targets(entries,Key.encode(query)),rank) == Some{value} : Maybe<&2,D.Value>}
  Origin<query,entries,rank,value>
def every_projected_output_has_an_original_matching_parts_source_position_and_exact_rank(query,entries,rank,value,found):
  match entries:
    case Nil{}: Empty.absurd(Origin<query,Nil{},rank,value>,F.none_negative_some(D.Value,value,found))
    case Con{+head,+tail}: head_case(query,Content.matches(Key.encode(query),head),head,tail,rank,value,{==},found,r => v => present => every_projected_output_has_an_original_matching_parts_source_position_and_exact_rank(query,tail,r,v,present))

law an_included_head_is_present_at_projection_zero:
  for +kept: Bool
  for +head: D.Value
  for +tail: List<&2,D.Value>
  for included: {kept == True{} : Bool}
  {Position.at(Sequence.include(kept,head,tail),0n) == Some{head} : Maybe<&2,D.Value>}
def an_included_head_is_present_at_projection_zero(kept,head,tail,included):
  Equal.cong(Bool,Maybe<&2,D.Value>,b => Position.at(Sequence.include(b,head,tail),0n),kept,True{},included)

law a_preceding_source_entry_shifts_tail_ranks_exactly_by_its_own_inclusion:
  for +kept: Bool
  for +head: D.Value
  for +tail: List<&2,D.Value>
  for +rank: Nat
  for +value: D.Value
  for found: {Position.at(tail,rank) == Some{value} : Maybe<&2,D.Value>}
  {Position.at(Sequence.include(kept,head,tail),advance(kept,rank)) == Some{value} : Maybe<&2,D.Value>}
def a_preceding_source_entry_shifts_tail_ranks_exactly_by_its_own_inclusion(kept,head,tail,rank,value,found):
  match kept:
    case False{}: found
    case True{}: found

law every_original_matching_parts_occurrence_is_retained_with_its_exact_payload_and_rank:
  for +query: List<&2,String>
  for +entries: List<&2,Source.SourceEntry>
  for +position: Nat
  for +entry: Source.SourceEntry
  for present: {Source.at(entries,position) == Some{entry} : Maybe<&2,Source.SourceEntry>}
  for matched: {query == Source.parts(entry) : List<&2,String>}
  {Position.at(Content.targets(entries,Key.encode(query)),before(entries,position,Key.encode(query))) == Some{D.VText{Source.target(entry)}} : Maybe<&2,D.Value>}
def every_original_matching_parts_occurrence_is_retained_with_its_exact_payload_and_rank(query,entries,position,entry,present,matched):
  match entries position:
    case Nil{} position: Empty.absurd({Position.at(Content.targets(Nil{},Key.encode(query)),before(Nil{},position,Key.encode(query))) == Some{D.VText{Source.target(entry)}} : Maybe<&2,D.Value>},F.none_negative_some(Source.SourceEntry,entry,present))
    case Con{+head,+tail} 0n:
      +same = F.some_injective(Source.SourceEntry,head,entry,present)
      Equal.trans(Maybe<&2,D.Value>,Position.at(Content.targets(Con{head,tail},Key.encode(query)),0n),Some{D.VText{Source.target(head)}},Some{D.VText{Source.target(entry)}},an_included_head_is_present_at_projection_zero(Content.matches(Key.encode(query),head),D.VText{Source.target(head)},Content.targets(tail,Key.encode(query)),literal_match_is_true(query,head,Equal.trans(List<&2,String>,query,Source.parts(entry),Source.parts(head),matched,Equal.cong(Source.SourceEntry,List<&2,String>,Source.parts,entry,head,Equal.sym(Source.SourceEntry,head,entry,same))))),Equal.cong(Source.SourceEntry,Maybe<&2,D.Value>,e => Some{D.VText{Source.target(e)}},head,entry,same))
    case Con{+head,+tail} 1n+previous: a_preceding_source_entry_shifts_tail_ranks_exactly_by_its_own_inclusion(Content.matches(Key.encode(query),head),D.VText{Source.target(head)},Content.targets(tail,Key.encode(query)),before(tail,previous,Key.encode(query)),D.VText{Source.target(entry)},every_original_matching_parts_occurrence_is_retained_with_its_exact_payload_and_rank(query,tail,previous,entry,present,matched))

law zero_is_strictly_before_an_included_source_prefix:
  for +kept: Bool
  for +tail: Nat
  for included: {kept == True{} : Bool}
  {Nat.is_lt(0n,advance(kept,tail)) == True{} : Bool}
def zero_is_strictly_before_an_included_source_prefix(kept,tail,included): Equal.cong(Bool,Bool,b => Nat.is_lt(0n,advance(b,tail)),kept,True{},included)

law shifting_both_ranks_by_the_same_inclusion_preserves_strict_order:
  for +kept: Bool
  for +first: Nat
  for +later: Nat
  for ordered: {Nat.is_lt(first,later) == True{} : Bool}
  {Nat.is_lt(advance(kept,first),advance(kept,later)) == True{} : Bool}
def shifting_both_ranks_by_the_same_inclusion_preserves_strict_order(kept,first,later,ordered):
  match kept:
    case False{}: ordered
    case True{}: ordered

law matching_original_source_positions_preserve_strict_projected_output_order:
  for +query: List<&2,String>
  for +entries: List<&2,Source.SourceEntry>
  for +first: Nat
  for +later: Nat
  for +first_entry: Source.SourceEntry
  for +later_entry: Source.SourceEntry
  for first_present: {Source.at(entries,first) == Some{first_entry} : Maybe<&2,Source.SourceEntry>}
  for later_present: {Source.at(entries,later) == Some{later_entry} : Maybe<&2,Source.SourceEntry>}
  for first_matched: {query == Source.parts(first_entry) : List<&2,String>}
  for later_matched: {query == Source.parts(later_entry) : List<&2,String>}
  for ordered: {Nat.is_lt(first,later) == True{} : Bool}
  {Nat.is_lt(before(entries,first,Key.encode(query)),before(entries,later,Key.encode(query))) == True{} : Bool}
def matching_original_source_positions_preserve_strict_projected_output_order(query,entries,first,later,first_entry,later_entry,first_present,later_present,first_matched,later_matched,ordered):
  match entries first later:
    case Nil{} first later: Empty.absurd({Nat.is_lt(before(Nil{},first,Key.encode(query)),before(Nil{},later,Key.encode(query))) == True{} : Bool},F.none_negative_some(Source.SourceEntry,first_entry,first_present))
    case Con{head,tail} 0n 0n: F.absurd_boolean({Nat.is_lt(0n,0n) == True{} : Bool},ordered)
    case Con{head,tail} 1n+first 0n: F.absurd_boolean({Nat.is_lt(before(Con{head,tail},1n+first,Key.encode(query)),0n) == True{} : Bool},ordered)
    case Con{+head,+tail} 0n 1n+later: zero_is_strictly_before_an_included_source_prefix(Content.matches(Key.encode(query),head),before(tail,later,Key.encode(query)),literal_match_is_true(query,head,Equal.trans(List<&2,String>,query,Source.parts(first_entry),Source.parts(head),first_matched,Equal.cong(Source.SourceEntry,List<&2,String>,Source.parts,first_entry,head,Equal.sym(Source.SourceEntry,head,first_entry,F.some_injective(Source.SourceEntry,head,first_entry,first_present))))))
    case Con{+head,+tail} 1n+first 1n+later: shifting_both_ranks_by_the_same_inclusion_preserves_strict_order(Content.matches(Key.encode(query),head),before(tail,first,Key.encode(query)),before(tail,later,Key.encode(query)),matching_original_source_positions_preserve_strict_projected_output_order(query,tail,first,later,first_entry,later_entry,first_present,later_present,first_matched,later_matched,ordered))

def matches_count(entries: List<&2,Source.SourceEntry>,+query: String) -> Nat:
  match entries:
    case Nil{}: 0n
    case Con{+head,tail}: advance(Content.matches(query,head),matches_count(tail,query))

def include_length(+kept: Bool,+head: D.Value,+tail: List<&2,D.Value>,+count: Nat,correct: {Sequence.length(tail) == count : Nat}) -> {Sequence.length(Sequence.include(kept,head,tail)) == advance(kept,count) : Nat}:
  match kept:
    case False{}: correct
    case True{}: Equal.cong(Nat,Nat,n => 1n+n,Sequence.length(tail),count,correct)

law projected_cardinality_is_exactly_the_number_of_matching_original_occurrences:
  for +entries: List<&2,Source.SourceEntry>
  for +query: String
  {Sequence.length(Content.targets(entries,query)) == matches_count(entries,query) : Nat}
def projected_cardinality_is_exactly_the_number_of_matching_original_occurrences(entries,query):
  match entries:
    case Nil{}: {==}
    case Con{+head,+tail}: include_length(Content.matches(query,head),D.VText{Source.target(head)},Content.targets(tail,query),matches_count(tail,query),projected_cardinality_is_exactly_the_number_of_matching_original_occurrences(tail,query))

def Meaning(+query: List<&2,String>,+entries: List<&2,Source.SourceEntry>,+result: List<&2,D.Value>) -> Type:
  L.E<{Sequence.length(result) == matches_count(entries,Key.encode(query)) : Nat},L.E<@+rank: Nat -> @+value: D.Value -> {Position.at(result,rank) == Some{value} : Maybe<&2,D.Value>} -> Origin<query,entries,rank,value>,@+position: Nat -> @+entry: Source.SourceEntry -> {Source.at(entries,position) == Some{entry} : Maybe<&2,Source.SourceEntry>} -> {query == Source.parts(entry) : List<&2,String>} -> {Position.at(result,before(entries,position,Key.encode(query))) == Some{D.VText{Source.target(entry)}} : Maybe<&2,D.Value>}>>

law independent_source_projection_has_exact_contents_multiplicity_and_original_index_meaning:
  for +query: List<&2,String>
  for +entries: List<&2,Source.SourceEntry>
  Meaning(query,entries,Content.targets(entries,Key.encode(query)))
def independent_source_projection_has_exact_contents_multiplicity_and_original_index_meaning(query,entries):
  L.Both{projected_cardinality_is_exactly_the_number_of_matching_original_occurrences(entries,Key.encode(query)),L.Both{rank => value => found => every_projected_output_has_an_original_matching_parts_source_position_and_exact_rank(query,entries,rank,value,found),position => entry => present => matched => every_original_matching_parts_occurrence_is_retained_with_its_exact_payload_and_rank(query,entries,position,entry,present,matched)}}
