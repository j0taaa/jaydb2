# Actual group keys are ordered by strictly DESCENDING greatest matching
# source positions. LastSource proves the independent positional meaning of
# each last() measure; this invariant does not assume group output order.
import Base
import ./SequenceLastSource.bend as Last
import ./SequenceGroupLookup.bend as Lookup
import ./SequenceSelectionProofs.bend as Selection
import ./SequenceGroupUniqueness.bend as U
import ./SequenceGroupMembers.bend as Members
import ./SequencePaginationProofs.bend as Position
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ./Sequence.bend as Sequence
import ../proof/Foundations.bend as F
import ../proof/Orders.bend as O

type Located<-result: Maybe<&2,Nat>> is Data:
  Located{position: Nat,exact: {result == Some{position} : Maybe<&2,Nat>}}

def Greater(first: Maybe<&2,Nat>,later: Maybe<&2,Nat>) -> Data:
  match first later:
    case Some{i} Some{j}: {Nat.is_lt(j,i) == True{} : Bool}
    case None{} Some{j}: {False{} == True{} : Bool}
    case Some{i} None{}: {False{} == True{} : Bool}
    case None{} None{}: {False{} == True{} : Bool}

def After(~key: D.Value -> String,+source: List<&2,D.Value>,+head: String,groups: List<&2,Sequence.Group>) -> Data:
  match groups:
    case Nil{}: Unit
    case Con{Sequence.Group{k,items},tail}: U.Both<Greater(Last.last(~key,head,source),Last.last(~key,k,source)),After(~key,source,head,tail)>

def Ordered(~key: D.Value -> String,+source: List<&2,D.Value>,groups: List<&2,Sequence.Group>) -> Data:
  match groups:
    case Nil{}: Unit
    case Con{Sequence.Group{+head,items},+tail}: U.Both<Located<Last.last(~key,head,source)>,U.Both<After(~key,source,head,tail),Ordered(~key,source,tail)>>

def represented_missing_is_empty(+items: List<&2,D.Value>,same: {Lookup.represented(items) == None{} : Maybe<&2,List<&2,D.Value>>}) -> {items == Nil{} : List<&2,D.Value>}:
  match items:
    case Nil{}: {==}
    case Con{+head,+tail}: L.ex_false({Con{head,tail} == Nil{} : List<&2,D.Value>},F.none_negative_some(List<&2,D.Value>,Con{head,tail},Equal.sym(Maybe<&2,List<&2,D.Value>>,Some{Con{head,tail}},None{},same)))

def last_missing_case(~key: D.Value -> String,+wanted: String,+source: List<&2,D.Value>,result: Maybe<&2,Nat>,actual: {Last.last(~key,wanted,source) == result : Maybe<&2,Nat>},correct: Last.Correct(~key,wanted,source,result),empty: {Lookup.for_key(~key,wanted,source) == Nil{} : List<&2,D.Value>}) -> {Last.last(~key,wanted,source) == None{} : Maybe<&2,Nat>}:
  match result:
    case None{}: actual
    case Some{+position}:
      match correct:
        case Tuple{+value,L.Both{present,L.Both{matched,greatest}}}:
          L.ex_false({Last.last(~key,wanted,source) == None{} : Maybe<&2,Nat>},F.none_negative_some(D.Value,value,
            Equal.trans(Maybe<&2,D.Value>,None{},Position.at(Lookup.for_key(~key,wanted,source),Selection.before(~Lookup.selected(~key),wanted,source,position)),Some{value},
              Equal.sym(Maybe<&2,D.Value>,Position.at(Lookup.for_key(~key,wanted,source),Selection.before(~Lookup.selected(~key),wanted,source,position)),None{},Equal.cong(List<&2,D.Value>,Maybe<&2,D.Value>,items => Position.at(items,Selection.before(~Lookup.selected(~key),wanted,source,position)),Lookup.for_key(~key,wanted,source),Nil{},empty)),Selection.every_matching_source_occurrence_is_retained_at_its_exact_rank(~Lookup.selected(~key),wanted,source,position,value,present,matched))))

law an_empty_key_class_has_no_last_matching_position:
  for ~key: D.Value -> String
  for +wanted: String
  for +source: List<&2,D.Value>
  for empty: {Lookup.represented(Lookup.for_key(~key,wanted,source)) == None{} : Maybe<&2,List<&2,D.Value>>}
  {Last.last(~key,wanted,source) == None{} : Maybe<&2,Nat>}
def an_empty_key_class_has_no_last_matching_position(key,wanted,source,empty):
  last_missing_case(~key,wanted,source,Last.last(~key,wanted,source),{==},Last.last_is_exactly_the_greatest_original_matching_position(~key,wanted,source),represented_missing_is_empty(Lookup.for_key(~key,wanted,source),empty))

def lift_location(~key: D.Value -> String,+x: D.Value,+source: List<&2,D.Value>,+wanted: String,located: Located<Last.last(~key,wanted,source)>) -> Located<Last.last(~key,wanted,Con{x,source})>:
  match located:
    case Located{+position,actual}: Located{1n+position,Equal.cong(Maybe<&2,Nat>,Maybe<&2,Nat>,result => Last.step(result,String.eq(wanted,key(x))),Last.last(~key,wanted,source),Some{position},actual)}

def lift_greater(first: Maybe<&2,Nat>,later: Maybe<&2,Nat>,+head_first: Bool,+head_later: Bool,greater: Greater(first,later)) -> Greater(Last.step(first,head_first),Last.step(later,head_later)):
  match first later:
    case Some{i} Some{j}: greater
    case None{} Some{j}: F.absurd_boolean(Greater(Last.step(None{},head_first),Some{1n+j}),greater)
    case Some{i} None{}: F.absurd_boolean(Greater(Some{1n+i},Last.step(None{},head_later)),greater)
    case None{} None{}: F.absurd_boolean(Greater(Last.step(None{},head_first),Last.step(None{},head_later)),greater)

def lift_after(~key: D.Value -> String,+x: D.Value,+source: List<&2,D.Value>,+head: String,+groups: List<&2,Sequence.Group>,after: After(~key,source,head,groups)) -> After(~key,Con{x,source},head,groups):
  match groups after:
    case Nil{} Unit{}: Unit{}
    case Con{Sequence.Group{+k,items},+tail} U.Both{greater,rest}: U.Both{lift_greater(Last.last(~key,head,source),Last.last(~key,k,source),String.eq(head,key(x)),String.eq(k,key(x)),greater),lift_after(~key,x,source,head,tail,rest)}

def lift_order(~key: D.Value -> String,+x: D.Value,+source: List<&2,D.Value>,+groups: List<&2,Sequence.Group>,ordered: Ordered(~key,source,groups)) -> Ordered(~key,Con{x,source},groups):
  match groups ordered:
    case Nil{} Unit{}: Unit{}
    case Con{Sequence.Group{+head,items},+tail} U.Both{located,U.Both{after,rest}}: U.Both{lift_location(~key,x,source,head,located),U.Both{lift_after(~key,x,source,head,tail,after),lift_order(~key,x,source,tail,rest)}}

def new_at_zero(~key: D.Value -> String,+x: D.Value,+source: List<&2,D.Value>,fresh: {Last.last(~key,key(x),source) == None{} : Maybe<&2,Nat>}) -> {Last.last(~key,key(x),Con{x,source}) == Some{0n} : Maybe<&2,Nat>}:
  Equal.trans(Maybe<&2,Nat>,Last.last(~key,key(x),Con{x,source}),Last.step(None{},String.eq(key(x),key(x))),Some{0n},Equal.cong(Maybe<&2,Nat>,Maybe<&2,Nat>,result => Last.step(result,String.eq(key(x),key(x))),Last.last(~key,key(x),source),None{},fresh),Equal.cong(Bool,Maybe<&2,Nat>,matches => Last.step(None{},matches),String.eq(key(x),key(x)),True{},O.string_eq_refl(key(x))))

def new_location(~key: D.Value -> String,+x: D.Value,+source: List<&2,D.Value>,fresh: {Last.last(~key,key(x),source) == None{} : Maybe<&2,Nat>}) -> Located<Last.last(~key,key(x),Con{x,source})>:
  Located{0n,new_at_zero(~key,x,source,fresh)}

def greater_at_known_positions(+first: Maybe<&2,Nat>,+later: Maybe<&2,Nat>,+i: Nat,+j: Nat,first_at: {first == Some{i} : Maybe<&2,Nat>},later_at: {later == Some{j} : Maybe<&2,Nat>},greater: {Nat.is_lt(j,i) == True{} : Bool}) -> Greater(first,later):
  %Equal.sym(Maybe<&2,Nat>,later,Some{j},later_at) : Greater(first,_)
  %Equal.sym(Maybe<&2,Nat>,first,Some{i},first_at) : Greater(_,Some{j})
  greater

def previous_location_precedes_new_location(~key: D.Value -> String,+x: D.Value,+source: List<&2,D.Value>,+head: String,located: Located<Last.last(~key,head,source)>,fresh: {Last.last(~key,key(x),source) == None{} : Maybe<&2,Nat>}) -> Greater(Last.last(~key,head,Con{x,source}),Last.last(~key,key(x),Con{x,source})):
  match located:
    case Located{+position,actual}:
      greater_at_known_positions(Last.last(~key,head,Con{x,source}),Last.last(~key,key(x),Con{x,source}),1n+position,0n,
            Equal.cong(Maybe<&2,Nat>,Maybe<&2,Nat>,result => Last.step(result,String.eq(head,key(x))),Last.last(~key,head,source),Some{position},actual),new_at_zero(~key,x,source,fresh),{==})

# Given exact per-key completeness, reaching the end of a registry proves the
# key is new to the source. All older keys have positive shifted positions.
def after_insertion_choice(~key: D.Value -> String,equal: Bool,+x: D.Value,+source: List<&2,D.Value>,+head: String,+k: String,+items: List<&2,D.Value>,+tail: List<&2,Sequence.Group>,actual: {String.eq(key(x),k) == equal : Bool},+located: Located<Last.last(~key,head,source)>,greater: Greater(Last.last(~key,head,source),Last.last(~key,k,source)),after: After(~key,source,head,tail),complete: {Lookup.lookup(key(x),Con{Sequence.Group{k,items},tail}) == Lookup.represented(Lookup.for_key(~key,key(x),source)) : Maybe<&2,List<&2,D.Value>>},recursive: {Lookup.lookup(key(x),tail) == Lookup.represented(Lookup.for_key(~key,key(x),source)) : Maybe<&2,List<&2,D.Value>>} -> After(~key,Con{x,source},head,Sequence.group_insert(key(x),x,tail))) ->
  After(~key,Con{x,source},head,Bool.pick(List<&2,Sequence.Group>,equal,Con{Sequence.Group{k,Con{x,items}},tail},Con{Sequence.Group{k,items},Sequence.group_insert(key(x),x,tail)})):
  match equal:
    case True{}: U.Both{lift_greater(Last.last(~key,head,source),Last.last(~key,k,source),String.eq(head,key(x)),String.eq(k,key(x)),greater),lift_after(~key,x,source,head,tail,after)}
    case False{}: U.Both{lift_greater(Last.last(~key,head,source),Last.last(~key,k,source),String.eq(head,key(x)),String.eq(k,key(x)),greater),recursive(
      Equal.trans(Maybe<&2,List<&2,D.Value>>,Lookup.lookup(key(x),tail),Lookup.lookup(key(x),Con{Sequence.Group{k,items},tail}),Lookup.represented(Lookup.for_key(~key,key(x),source)),Equal.sym(Maybe<&2,List<&2,D.Value>>,Lookup.lookup(key(x),Con{Sequence.Group{k,items},tail}),Lookup.lookup(key(x),tail),Lookup.head_lookup_given(False{},key(x),k,items,tail,actual)),complete))}

law after_inserting:
  for ~key: D.Value -> String
  for +x: D.Value
  for +source: List<&2,D.Value>
  for +head: String
  for +groups: List<&2,Sequence.Group>
  for +located: Located<Last.last(~key,head,source)>
  for after: After(~key,source,head,groups)
  for complete: {Lookup.lookup(key(x),groups) == Lookup.represented(Lookup.for_key(~key,key(x),source)) : Maybe<&2,List<&2,D.Value>>}
  After(~key,Con{x,source},head,Sequence.group_insert(key(x),x,groups))

def after_inserting(key,x,source,head,groups,located,after,complete):
  match groups after:
    case Nil{} Unit{}: U.Both{previous_location_precedes_new_location(~key,x,source,head,located,an_empty_key_class_has_no_last_matching_position(~key,key(x),source,Equal.sym(Maybe<&2,List<&2,D.Value>>,None{},Lookup.represented(Lookup.for_key(~key,key(x),source)),complete))),Unit{}}
    case Con{Sequence.Group{+k,+items},+tail} U.Both{greater,+rest}: after_insertion_choice(~key,String.eq(key(x),k),x,source,head,k,items,tail,{==},located,greater,rest,complete,tail_complete => after_inserting(~key,x,source,head,tail,located,rest,tail_complete))

def ordered_insertion_choice(~key: D.Value -> String,equal: Bool,+x: D.Value,+source: List<&2,D.Value>,+head: String,+items: List<&2,D.Value>,+tail: List<&2,Sequence.Group>,actual: {String.eq(key(x),head) == equal : Bool},+located: Located<Last.last(~key,head,source)>,after: After(~key,source,head,tail),rest: Ordered(~key,source,tail),complete: {Lookup.lookup(key(x),Con{Sequence.Group{head,items},tail}) == Lookup.represented(Lookup.for_key(~key,key(x),source)) : Maybe<&2,List<&2,D.Value>>},recursive: {Lookup.lookup(key(x),tail) == Lookup.represented(Lookup.for_key(~key,key(x),source)) : Maybe<&2,List<&2,D.Value>>} -> Ordered(~key,Con{x,source},Sequence.group_insert(key(x),x,tail))) ->
  Ordered(~key,Con{x,source},Bool.pick(List<&2,Sequence.Group>,equal,Con{Sequence.Group{head,Con{x,items}},tail},Con{Sequence.Group{head,items},Sequence.group_insert(key(x),x,tail)})):
  match equal:
    case True{}: U.Both{lift_location(~key,x,source,head,located),U.Both{lift_after(~key,x,source,head,tail,after),lift_order(~key,x,source,tail,rest)}}
    case False{}:
      +tail_complete = Equal.trans(Maybe<&2,List<&2,D.Value>>,Lookup.lookup(key(x),tail),Lookup.lookup(key(x),Con{Sequence.Group{head,items},tail}),Lookup.represented(Lookup.for_key(~key,key(x),source)),Equal.sym(Maybe<&2,List<&2,D.Value>>,Lookup.lookup(key(x),Con{Sequence.Group{head,items},tail}),Lookup.lookup(key(x),tail),Lookup.head_lookup_given(False{},key(x),head,items,tail,actual)),complete)
      U.Both{lift_location(~key,x,source,head,located),U.Both{after_inserting(~key,x,source,head,tail,located,after,tail_complete),recursive(tail_complete)}}

law ordered_inserting:
  for ~key: D.Value -> String
  for +x: D.Value
  for +source: List<&2,D.Value>
  for +groups: List<&2,Sequence.Group>
  for ordered: Ordered(~key,source,groups)
  for complete: {Lookup.lookup(key(x),groups) == Lookup.represented(Lookup.for_key(~key,key(x),source)) : Maybe<&2,List<&2,D.Value>>}
  Ordered(~key,Con{x,source},Sequence.group_insert(key(x),x,groups))

def ordered_inserting(key,x,source,groups,ordered,complete):
  match groups ordered:
    case Nil{} Unit{}: U.Both{new_location(~key,x,source,an_empty_key_class_has_no_last_matching_position(~key,key(x),source,Equal.sym(Maybe<&2,List<&2,D.Value>>,None{},Lookup.represented(Lookup.for_key(~key,key(x),source)),complete))),U.Both{Unit{},Unit{}}}
    case Con{Sequence.Group{+head,+items},+tail} U.Both{located,U.Both{after,+rest}}: ordered_insertion_choice(~key,String.eq(key(x),head),x,source,head,items,tail,{==},located,after,rest,complete,tail_complete => ordered_inserting(~key,x,source,tail,rest,tail_complete))

law actual_group_keys_are_in_strict_descending_last_occurrence_order:
  for ~key: D.Value -> String
  for +xs: List<&2,D.Value>
  Ordered(~key,xs,Sequence.group(~key,xs))
def actual_group_keys_are_in_strict_descending_last_occurrence_order(key,xs):
  match xs:
    case Nil{}: Unit{}
    case Con{+x,+tail}: ordered_inserting(~key,x,tail,Sequence.group(~key,tail),actual_group_keys_are_in_strict_descending_last_occurrence_order(~key,tail),Lookup.actual_group_lookup_is_exactly_all_original_matching_occurrences(~key,key(x),tail))

law actual_group_has_complete_independent_members_and_last_occurrence_order:
  for ~key: D.Value -> String
  for +xs: List<&2,D.Value>
  L.E<Members.Meaning(~key,xs,Sequence.group(~key,xs)),Ordered(~key,xs,Sequence.group(~key,xs))>
def actual_group_has_complete_independent_members_and_last_occurrence_order(key,xs):
  L.Both{Members.actual_group_has_unique_complete_keys_and_exact_ordered_members(~key,xs),actual_group_keys_are_in_strict_descending_last_occurrence_order(~key,xs)}
