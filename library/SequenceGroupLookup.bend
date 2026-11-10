# Independent per-key observation of groups, linked to the already proved
# indexed filter specification. Querying an absent key returns None; querying
# a present key returns EVERY original matching occurrence in original order.
import Base
import ./SequenceSelectionProofs.bend as Selection
import ../contract/Data.bend as D
import ./Sequence.bend as Sequence
import ../proof/Foundations.bend as F
import ../proof/Orders.bend as O

def lookup(+wanted: String,groups: List<&2,Sequence.Group>) -> Maybe<&2,List<&2,D.Value>>:
  match groups:
    case Nil{}: None{}
    case Con{Sequence.Group{key,items},tail}: Bool.pick(Maybe<&2,List<&2,D.Value>>,String.eq(wanted,key),Some{items},lookup(wanted,tail))

def pushed(x: D.Value,previous: Maybe<&2,List<&2,D.Value>>) -> Maybe<&2,List<&2,D.Value>>:
  match previous:
    case None{}: Some{[x]}
    case Some{items}: Some{Con{x,items}}

def represented(items: List<&2,D.Value>) -> Maybe<&2,List<&2,D.Value>>:
  match items:
    case Nil{}: None{}
    case Con{x,tail}: Some{Con{x,tail}}

def selected(~key: D.Value -> String,wanted: String,value: D.Value) -> Bool:
  String.eq(wanted,key(value))

def for_key(~key: D.Value -> String,+wanted: String,xs: List<&2,D.Value>) -> List<&2,D.Value>:
  Selection.select(~selected(~key),wanted,xs)

def head_lookup_given(flag: Bool,+wanted: String,+key: String,+items: List<&2,D.Value>,+tail: List<&2,Sequence.Group>,actual: {String.eq(wanted,key) == flag : Bool}) ->
  {lookup(wanted,Con{Sequence.Group{key,items},tail}) == Bool.pick(Maybe<&2,List<&2,D.Value>>,flag,Some{items},lookup(wanted,tail)) : Maybe<&2,List<&2,D.Value>>}:
  Equal.cong(Bool,Maybe<&2,List<&2,D.Value>>,choice => Bool.pick(Maybe<&2,List<&2,D.Value>>,choice,Some{items},lookup(wanted,tail)),String.eq(wanted,key),flag,actual)

def own_key_choice(equal: Bool,+key: String,+x: D.Value,+head: String,+items: List<&2,D.Value>,+tail: List<&2,Sequence.Group>,+actual: {String.eq(key,head) == equal : Bool},
  recursive: {lookup(key,Sequence.group_insert(key,x,tail)) == pushed(x,lookup(key,tail)) : Maybe<&2,List<&2,D.Value>>}) ->
  {lookup(key,Bool.pick(List<&2,Sequence.Group>,equal,Con{Sequence.Group{head,Con{x,items}},tail},Con{Sequence.Group{head,items},Sequence.group_insert(key,x,tail)})) == pushed(x,lookup(key,Con{Sequence.Group{head,items},tail})) : Maybe<&2,List<&2,D.Value>>}:
  match equal:
    case True{}:
      Equal.trans(Maybe<&2,List<&2,D.Value>>,lookup(key,Con{Sequence.Group{head,Con{x,items}},tail}),Some{Con{x,items}},pushed(x,lookup(key,Con{Sequence.Group{head,items},tail})),head_lookup_given(True{},key,head,Con{x,items},tail,actual),
        Equal.sym(Maybe<&2,List<&2,D.Value>>,pushed(x,lookup(key,Con{Sequence.Group{head,items},tail})),Some{Con{x,items}},Equal.cong(Maybe<&2,List<&2,D.Value>>,Maybe<&2,List<&2,D.Value>>,previous => pushed(x,previous),lookup(key,Con{Sequence.Group{head,items},tail}),Some{items},head_lookup_given(True{},key,head,items,tail,actual))))
    case False{}:
      Equal.trans(Maybe<&2,List<&2,D.Value>>,lookup(key,Con{Sequence.Group{head,items},Sequence.group_insert(key,x,tail)}),lookup(key,Sequence.group_insert(key,x,tail)),pushed(x,lookup(key,Con{Sequence.Group{head,items},tail})),head_lookup_given(False{},key,head,items,Sequence.group_insert(key,x,tail),actual),
        Equal.trans(Maybe<&2,List<&2,D.Value>>,lookup(key,Sequence.group_insert(key,x,tail)),pushed(x,lookup(key,tail)),pushed(x,lookup(key,Con{Sequence.Group{head,items},tail})),recursive,Equal.sym(Maybe<&2,List<&2,D.Value>>,pushed(x,lookup(key,Con{Sequence.Group{head,items},tail})),pushed(x,lookup(key,tail)),Equal.cong(Maybe<&2,List<&2,D.Value>>,Maybe<&2,List<&2,D.Value>>,previous => pushed(x,previous),lookup(key,Con{Sequence.Group{head,items},tail}),lookup(key,tail),head_lookup_given(False{},key,head,items,tail,actual)))))

law inserting_a_key_prepends_its_value_to_that_keys_observation:
  for +key: String
  for +x: D.Value
  for +groups: List<&2,Sequence.Group>
  {lookup(key,Sequence.group_insert(key,x,groups)) == pushed(x,lookup(key,groups)) : Maybe<&2,List<&2,D.Value>>}
def inserting_a_key_prepends_its_value_to_that_keys_observation(key,x,groups):
  match groups:
    case Nil{}: head_lookup_given(True{},key,key,[x],Nil{},O.string_eq_refl(key))
    case Con{Sequence.Group{+head,+items},+tail}: own_key_choice(String.eq(key,head),key,x,head,items,tail,{==},inserting_a_key_prepends_its_value_to_that_keys_observation(key,x,tail))

def different_query_choice(equal: Bool,matched: Bool,+wanted: String,+key: String,+x: D.Value,+head: String,+items: List<&2,D.Value>,+tail: List<&2,Sequence.Group>,
  +actual_key: {String.eq(key,head) == equal : Bool},+actual_query: {String.eq(wanted,head) == matched : Bool},different: {String.eq(wanted,key) == False{} : Bool},
  recursive: {lookup(wanted,Sequence.group_insert(key,x,tail)) == lookup(wanted,tail) : Maybe<&2,List<&2,D.Value>>}) ->
  {lookup(wanted,Bool.pick(List<&2,Sequence.Group>,equal,Con{Sequence.Group{head,Con{x,items}},tail},Con{Sequence.Group{head,items},Sequence.group_insert(key,x,tail)})) == lookup(wanted,Con{Sequence.Group{head,items},tail}) : Maybe<&2,List<&2,D.Value>>}:
  match equal matched:
    case True{} True{}:
      F.absurd_boolean({lookup(wanted,Con{Sequence.Group{head,Con{x,items}},tail}) == lookup(wanted,Con{Sequence.Group{head,items},tail}) : Maybe<&2,List<&2,D.Value>>},
        Equal.trans(Bool,False{},String.eq(wanted,key),True{},Equal.sym(Bool,String.eq(wanted,key),False{},different),Equal.trans(Bool,String.eq(wanted,key),String.eq(wanted,head),True{},Equal.cong(String,Bool,k => String.eq(wanted,k),key,head,O.string_equal(key,head,actual_key)),actual_query)))
    case True{} False{}:
      Equal.trans(Maybe<&2,List<&2,D.Value>>,lookup(wanted,Con{Sequence.Group{head,Con{x,items}},tail}),lookup(wanted,tail),lookup(wanted,Con{Sequence.Group{head,items},tail}),head_lookup_given(False{},wanted,head,Con{x,items},tail,actual_query),Equal.sym(Maybe<&2,List<&2,D.Value>>,lookup(wanted,Con{Sequence.Group{head,items},tail}),lookup(wanted,tail),head_lookup_given(False{},wanted,head,items,tail,actual_query)))
    case False{} True{}:
      Equal.trans(Maybe<&2,List<&2,D.Value>>,lookup(wanted,Con{Sequence.Group{head,items},Sequence.group_insert(key,x,tail)}),Some{items},lookup(wanted,Con{Sequence.Group{head,items},tail}),head_lookup_given(True{},wanted,head,items,Sequence.group_insert(key,x,tail),actual_query),Equal.sym(Maybe<&2,List<&2,D.Value>>,lookup(wanted,Con{Sequence.Group{head,items},tail}),Some{items},head_lookup_given(True{},wanted,head,items,tail,actual_query)))
    case False{} False{}:
      Equal.trans(Maybe<&2,List<&2,D.Value>>,lookup(wanted,Con{Sequence.Group{head,items},Sequence.group_insert(key,x,tail)}),lookup(wanted,Sequence.group_insert(key,x,tail)),lookup(wanted,Con{Sequence.Group{head,items},tail}),head_lookup_given(False{},wanted,head,items,Sequence.group_insert(key,x,tail),actual_query),
        Equal.trans(Maybe<&2,List<&2,D.Value>>,lookup(wanted,Sequence.group_insert(key,x,tail)),lookup(wanted,tail),lookup(wanted,Con{Sequence.Group{head,items},tail}),recursive,Equal.sym(Maybe<&2,List<&2,D.Value>>,lookup(wanted,Con{Sequence.Group{head,items},tail}),lookup(wanted,tail),head_lookup_given(False{},wanted,head,items,tail,actual_query))))

law inserting_a_different_key_preserves_the_querys_observation:
  for +wanted: String
  for +key: String
  for +x: D.Value
  for +groups: List<&2,Sequence.Group>
  for +different: {String.eq(wanted,key) == False{} : Bool}
  {lookup(wanted,Sequence.group_insert(key,x,groups)) == lookup(wanted,groups) : Maybe<&2,List<&2,D.Value>>}
def inserting_a_different_key_preserves_the_querys_observation(wanted,key,x,groups,different):
  match groups:
    case Nil{}: head_lookup_given(False{},wanted,key,[x],Nil{},different)
    case Con{Sequence.Group{+head,+items},+tail}: different_query_choice(String.eq(key,head),String.eq(wanted,head),wanted,key,x,head,items,tail,{==},{==},different,inserting_a_different_key_preserves_the_querys_observation(wanted,key,x,tail,different))

def query_choice(equal: Bool,+wanted: String,+key: String,+x: D.Value,+groups: List<&2,Sequence.Group>,actual: {String.eq(wanted,key) == equal : Bool}) ->
  {lookup(wanted,Sequence.group_insert(key,x,groups)) == Bool.pick(Maybe<&2,List<&2,D.Value>>,equal,pushed(x,lookup(wanted,groups)),lookup(wanted,groups)) : Maybe<&2,List<&2,D.Value>>}:
  match equal:
    case False{}: inserting_a_different_key_preserves_the_querys_observation(wanted,key,x,groups,actual)
    case True{}:
      %Equal.sym(String,wanted,key,O.string_equal(wanted,key,actual)) : {lookup(_,Sequence.group_insert(key,x,groups)) == pushed(x,lookup(_,groups)) : Maybe<&2,List<&2,D.Value>>}
      inserting_a_key_prepends_its_value_to_that_keys_observation(key,x,groups)

law actual_group_insert_has_exact_keyed_observations:
  for +wanted: String
  for +key: String
  for +x: D.Value
  for +groups: List<&2,Sequence.Group>
  {lookup(wanted,Sequence.group_insert(key,x,groups)) == Bool.pick(Maybe<&2,List<&2,D.Value>>,String.eq(wanted,key),pushed(x,lookup(wanted,groups)),lookup(wanted,groups)) : Maybe<&2,List<&2,D.Value>>}
def actual_group_insert_has_exact_keyed_observations(wanted,key,x,groups):
  query_choice(String.eq(wanted,key),wanted,key,x,groups,{==})

law pushed_observation_represents_a_prepended_occurrence:
  for +x: D.Value
  for +items: List<&2,D.Value>
  {pushed(x,represented(items)) == Some{Con{x,items}} : Maybe<&2,List<&2,D.Value>>}
def pushed_observation_represents_a_prepended_occurrence(x,items):
  match items:
    case Nil{}: {==}
    case Con{head,tail}: {==}

def represented_include(selected: Bool,+x: D.Value,+items: List<&2,D.Value>) ->
  {Bool.pick(Maybe<&2,List<&2,D.Value>>,selected,pushed(x,represented(items)),represented(items)) == represented(Sequence.include(selected,x,items)) : Maybe<&2,List<&2,D.Value>>}:
  match selected:
    case False{}: {==}
    case True{}: pushed_observation_represents_a_prepended_occurrence(x,items)

def query_update(+selected: Bool,+x: D.Value,+previous: Maybe<&2,List<&2,D.Value>>) -> Maybe<&2,List<&2,D.Value>>:
  Bool.pick(Maybe<&2,List<&2,D.Value>>,selected,pushed(x,previous),previous)

law actual_group_lookup_is_exactly_all_original_matching_occurrences:
  for ~key: D.Value -> String
  for +wanted: String
  for +xs: List<&2,D.Value>
  {lookup(wanted,Sequence.group(~key,xs)) == represented(for_key(~key,wanted,xs)) : Maybe<&2,List<&2,D.Value>>}
def actual_group_lookup_is_exactly_all_original_matching_occurrences(key,wanted,xs):
  match xs:
    case Nil{}: {==}
    case Con{+x,+tail}:
      Equal.trans(Maybe<&2,List<&2,D.Value>>,lookup(wanted,Sequence.group(~key,Con{x,tail})),query_update(String.eq(wanted,key(x)),x,lookup(wanted,Sequence.group(~key,tail))),represented(for_key(~key,wanted,Con{x,tail})),actual_group_insert_has_exact_keyed_observations(wanted,key(x),x,Sequence.group(~key,tail)),
        Equal.trans(Maybe<&2,List<&2,D.Value>>,query_update(String.eq(wanted,key(x)),x,lookup(wanted,Sequence.group(~key,tail))),query_update(String.eq(wanted,key(x)),x,represented(for_key(~key,wanted,tail))),represented(for_key(~key,wanted,Con{x,tail})),
          Equal.cong(Maybe<&2,List<&2,D.Value>>,Maybe<&2,List<&2,D.Value>>,previous => query_update(String.eq(wanted,key(x)),x,previous),lookup(wanted,Sequence.group(~key,tail)),represented(for_key(~key,wanted,tail)),actual_group_lookup_is_exactly_all_original_matching_occurrences(~key,wanted,tail)),represented_include(String.eq(wanted,key(x)),x,for_key(~key,wanted,tail))))
