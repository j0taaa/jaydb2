# Independent logical source entries. Their actual rows use the documented
# three fields, while source positions and duplicate-key exclusion are stated
# independently of lookup or a completed scan result. Custom derived-row keys
# are allowed; mode/arity is not silently inferred from a single row.
import Base
import ../contract/Data.bend as D
import ./Index.bend as Index
import ../proof/Foundations.bend as F
import ../proof/Orders.bend as O

type SourceEntry is Data:
  SourceEntry{key: String,parts: List<&2,String>,target: String}

def key(entry: SourceEntry) -> String:
  match entry:
    case SourceEntry{key,parts,target}: key

def parts(entry: SourceEntry) -> List<&2,String>:
  match entry:
    case SourceEntry{key,parts,target}: parts

def target(entry: SourceEntry) -> String:
  match entry:
    case SourceEntry{key,parts,target}: target

def raw(entry: SourceEntry) -> D.Row:
  match entry:
    case SourceEntry{key,parts,target}: Index.entry(key,parts,target)

def rows(entries: List<&2,SourceEntry>) -> List<&2,D.Row>:
  match entries:
    case Nil{}: Nil{}
    case Con{entry,tail}: Con{raw(entry),rows(tail)}

def keys(entries: List<&2,SourceEntry>) -> List<&2,String>:
  match entries:
    case Nil{}: Nil{}
    case Con{entry,tail}: Con{key(entry),keys(tail)}

def at(entries: List<&2,SourceEntry>,position: Nat) -> Maybe<&2,SourceEntry>:
  match entries position:
    case Nil{} position: None{}
    case Con{head,tail} 0n: Some{head}
    case Con{head,tail} 1n+previous: at(tail,previous)

def different(+wanted: String,entries: List<&2,SourceEntry>) -> Bool:
  match entries:
    case Nil{}: True{}
    case Con{head,tail}: Bool.not(String.eq(wanted,key(head))) && different(wanted,tail)

def unique(entries: List<&2,SourceEntry>) -> Bool:
  match entries:
    case Nil{}: True{}
    case Con{head,+tail}: different(key(head),tail) && unique(tail)

def unicode_keys(entries: List<&2,SourceEntry>) -> Bool:
  match entries:
    case Nil{}: True{}
    case Con{head,tail}: D.unicode_valid(key(head)) && unicode_keys(tail)

law independent_source_keys_are_exactly_the_actual_row_enumeration_order:
  for +entries: List<&2,SourceEntry>
  {D.keys_rows(rows(entries)) == keys(entries) : List<&2,String>}
def independent_source_keys_are_exactly_the_actual_row_enumeration_order(entries):
  match entries:
    case Nil{}: {==}
    case Con{SourceEntry{+key,parts,target},+tail}: Equal.cong(List<&2,String>,List<&2,String>,keys => Con{key,keys},D.keys_rows(rows(tail)),keys(tail),independent_source_keys_are_exactly_the_actual_row_enumeration_order(tail))

law every_present_source_entry_differs_from_a_globally_excluded_key:
  for +entries: List<&2,SourceEntry>
  for +position: Nat
  for +entry: SourceEntry
  for +wanted: String
  for +absent: {different(wanted,entries) == True{} : Bool}
  for present: {at(entries,position) == Some{entry} : Maybe<&2,SourceEntry>}
  {String.eq(wanted,key(entry)) == False{} : Bool}
def every_present_source_entry_differs_from_a_globally_excluded_key(entries,position,entry,wanted,absent,present):
  match entries position:
    case Nil{} position: Empty.absurd({String.eq(wanted,key(entry)) == False{} : Bool},F.none_negative_some(SourceEntry,entry,present))
    case Con{+head,+tail} 0n: Equal.trans(Bool,String.eq(wanted,key(entry)),String.eq(wanted,key(head)),False{},Equal.cong(SourceEntry,Bool,e => String.eq(wanted,key(e)),entry,head,Equal.sym(SourceEntry,head,entry,F.some_injective(SourceEntry,head,entry,present))),F.negation_true(String.eq(wanted,key(head)),F.and_boolean_left(Bool.not(String.eq(wanted,key(head))),different(wanted,tail),absent)))
    case Con{+head,+tail} 1n+previous: every_present_source_entry_differs_from_a_globally_excluded_key(tail,previous,entry,wanted,F.and_boolean_right(Bool.not(String.eq(wanted,key(head))),different(wanted,tail),absent),present)

law an_indexed_source_key_is_unicode_valid_when_all_source_keys_are:
  for +entries: List<&2,SourceEntry>
  for +position: Nat
  for +entry: SourceEntry
  for +valid: {unicode_keys(entries) == True{} : Bool}
  for present: {at(entries,position) == Some{entry} : Maybe<&2,SourceEntry>}
  {D.unicode_valid(key(entry)) == True{} : Bool}
def an_indexed_source_key_is_unicode_valid_when_all_source_keys_are(entries,position,entry,valid,present):
  match entries position:
    case Nil{} position: Empty.absurd({D.unicode_valid(key(entry)) == True{} : Bool},F.none_negative_some(SourceEntry,entry,present))
    case Con{+head,+tail} 0n: Equal.trans(Bool,D.unicode_valid(key(entry)),D.unicode_valid(key(head)),True{},Equal.cong(SourceEntry,Bool,e => D.unicode_valid(key(e)),entry,head,Equal.sym(SourceEntry,head,entry,F.some_injective(SourceEntry,head,entry,present))),F.and_boolean_left(D.unicode_valid(key(head)),unicode_keys(tail),valid))
    case Con{+head,+tail} 1n+previous: an_indexed_source_key_is_unicode_valid_when_all_source_keys_are(tail,previous,entry,F.and_boolean_right(D.unicode_valid(key(head)),unicode_keys(tail),valid),present)

law a_source_head_is_found_at_its_own_key:
  for +head: SourceEntry
  for +tail: List<&2,SourceEntry>
  {D.find_row(rows(Con{head,tail}),key(head)) == Some{raw(head)} : Maybe<&2,D.Row>}
def a_source_head_is_found_at_its_own_key(head,tail):
  match head:
    case SourceEntry{+key,+parts,+target}: Equal.cong(Bool,Maybe<&2,D.Row>,equal => Bool.pick(Maybe<&2,D.Row>,equal,Some{Index.entry(key,parts,target)},D.find_row(rows(tail),key)),String.eq(key,key),True{},O.string_eq_refl(key))

law a_mismatched_source_head_does_not_change_row_lookup:
  for +head: SourceEntry
  for +tail: List<&2,SourceEntry>
  for +wanted: String
  for absent: {String.eq(key(head),wanted) == False{} : Bool}
  {D.find_row(rows(Con{head,tail}),wanted) == D.find_row(rows(tail),wanted) : Maybe<&2,D.Row>}
def a_mismatched_source_head_does_not_change_row_lookup(head,tail,wanted,absent):
  match head:
    case SourceEntry{+key,+parts,+target}: Equal.cong(Bool,Maybe<&2,D.Row>,equal => Bool.pick(Maybe<&2,D.Row>,equal,Some{Index.entry(key,parts,target)},D.find_row(rows(tail),wanted)),String.eq(key,wanted),False{},absent)

law every_unique_source_occurrence_has_its_exact_key_lookup_and_complete_row_payload:
  for +entries: List<&2,SourceEntry>
  for +position: Nat
  for +entry: SourceEntry
  for +unique_keys: {unique(entries) == True{} : Bool}
  for +present: {at(entries,position) == Some{entry} : Maybe<&2,SourceEntry>}
  {D.find_row(rows(entries),key(entry)) == Some{raw(entry)} : Maybe<&2,D.Row>}
def every_unique_source_occurrence_has_its_exact_key_lookup_and_complete_row_payload(entries,position,entry,unique_keys,present):
  match entries position:
    case Nil{} position: Empty.absurd({D.find_row(rows(Nil{}),key(entry)) == Some{raw(entry)} : Maybe<&2,D.Row>},F.none_negative_some(SourceEntry,entry,present))
    case Con{+head,+tail} 0n:
      +same = F.some_injective(SourceEntry,head,entry,present)
      Equal.trans(Maybe<&2,D.Row>,D.find_row(rows(Con{head,tail}),key(entry)),D.find_row(rows(Con{head,tail}),key(head)),Some{raw(entry)},Equal.cong(String,Maybe<&2,D.Row>,wanted => D.find_row(rows(Con{head,tail}),wanted),key(entry),key(head),Equal.cong(SourceEntry,String,key,entry,head,Equal.sym(SourceEntry,head,entry,same))),Equal.trans(Maybe<&2,D.Row>,D.find_row(rows(Con{head,tail}),key(head)),Some{raw(head)},Some{raw(entry)},a_source_head_is_found_at_its_own_key(head,tail),Equal.cong(SourceEntry,Maybe<&2,D.Row>,e => Some{raw(e)},head,entry,same)))
    case Con{+head,+tail} 1n+previous:
      Equal.trans(Maybe<&2,D.Row>,D.find_row(rows(Con{head,tail}),key(entry)),D.find_row(rows(tail),key(entry)),Some{raw(entry)},a_mismatched_source_head_does_not_change_row_lookup(head,tail,key(entry),every_present_source_entry_differs_from_a_globally_excluded_key(tail,previous,entry,key(head),F.and_boolean_left(different(key(head),tail),unique(tail),unique_keys),present)),every_unique_source_occurrence_has_its_exact_key_lookup_and_complete_row_payload(tail,previous,entry,F.and_boolean_right(different(key(head),tail),unique(tail),unique_keys),present))

def rest(entries: List<&2,SourceEntry>) -> List<&2,SourceEntry>:
  match entries:
    case Nil{}: Nil{}
    case Con{head,tail}: tail

def drop(entries: List<&2,SourceEntry>,offset: Nat) -> List<&2,SourceEntry>:
  match entries offset:
    case Nil{} offset: Nil{}
    case Con{head,tail} 0n: Con{head,tail}
    case Con{head,tail} 1n+previous: drop(tail,previous)

law input_index_lookup_is_exactly_the_head_of_its_input_suffix:
  for +entries: List<&2,SourceEntry>
  for +offset: Nat
  {at(entries,offset) == at(drop(entries,offset),0n) : Maybe<&2,SourceEntry>}
def input_index_lookup_is_exactly_the_head_of_its_input_suffix(entries,offset):
  match entries offset:
    case Nil{} offset: {==}
    case Con{head,tail} 0n: {==}
    case Con{head,+tail} 1n+previous: input_index_lookup_is_exactly_the_head_of_its_input_suffix(tail,previous)

law dropping_zero_input_entries_is_identity:
  for +entries: List<&2,SourceEntry>
  {drop(entries,0n) == entries : List<&2,SourceEntry>}
def dropping_zero_input_entries_is_identity(entries):
  match entries:
    case Nil{}: {==}
    case Con{head,tail}: {==}

law advancing_an_input_index_is_exactly_dropping_its_current_suffix_head:
  for +entries: List<&2,SourceEntry>
  for +offset: Nat
  {drop(entries,1n+offset) == rest(drop(entries,offset)) : List<&2,SourceEntry>}
def advancing_an_input_index_is_exactly_dropping_its_current_suffix_head(entries,offset):
  match entries offset:
    case Nil{} offset: {==}
    case Con{head,+tail} 0n: dropping_zero_input_entries_is_identity(tail)
    case Con{head,+tail} 1n+previous: advancing_an_input_index_is_exactly_dropping_its_current_suffix_head(tail,previous)
