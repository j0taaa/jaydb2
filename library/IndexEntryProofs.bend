# Exact index-entry payloads and schema compatibility. Key encoding is over
# all character DATA; successful storage separately needs valid Unicode parts
# and target. No string normalization, truncation, or format change is assumed.
import Base
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ./Index.bend as Index
import ./Key.bend as Key
import ../proof/Foundations.bend as F
import ../proof/Orders.bend as O

def parts_valid(parts: List<&2,String>) -> Bool:
  match parts:
    case Nil{}: True{}
    case Con{head,tail}: D.unicode_valid(head) && parts_valid(tail)

law encoding_one_valid_part_preserves_the_valid_tail:
  for +part: String
  for +tail: String
  for +valid_part: {D.unicode_valid(part) == True{} : Bool}
  for +valid_tail: {D.unicode_valid(tail) == True{} : Bool}
  {D.unicode_valid(Key.part(part,tail)) == True{} : Bool}
def encoding_one_valid_part_preserves_the_valid_tail(part,tail,valid_part,valid_tail):
  match part:
    case SNil{}: valid_tail
    case SCon{Chr{+n},+rest}: F.and_boolean_intro(D.scalar_valid(n),D.unicode_valid(Key.part(rest,tail)),F.and_boolean_left(D.scalar_valid(n),D.unicode_valid(rest),valid_part),encoding_one_valid_part_preserves_the_valid_tail(rest,tail,F.and_boolean_right(D.scalar_valid(n),D.unicode_valid(rest),valid_part),valid_tail))

law encoding_valid_parts_always_produces_a_valid_unicode_row_key:
  for +parts: List<&2,String>
  for +valid: {parts_valid(parts) == True{} : Bool}
  {D.unicode_valid(Key.encode(parts)) == True{} : Bool}
def encoding_valid_parts_always_produces_a_valid_unicode_row_key(parts,valid):
  match parts:
    case Nil{}: {==}
    case Con{+head,+tail}: encoding_one_valid_part_preserves_the_valid_tail(head,Key.encode(tail),F.and_boolean_left(D.unicode_valid(head),parts_valid(tail),valid),encoding_valid_parts_always_produces_a_valid_unicode_row_key(tail,F.and_boolean_right(D.unicode_valid(head),parts_valid(tail),valid)))

law appending_valid_parts_preserves_unicode_validity:
  for +parts: List<&2,String>
  for +tail: List<&2,String>
  for +valid_parts: {parts_valid(parts) == True{} : Bool}
  for +valid_tail: {parts_valid(tail) == True{} : Bool}
  {parts_valid(Index.append(parts,tail)) == True{} : Bool}
def appending_valid_parts_preserves_unicode_validity(parts,tail,valid_parts,valid_tail):
  match parts:
    case Nil{}: valid_tail
    case Con{+head,+rest}: F.and_boolean_intro(D.unicode_valid(head),parts_valid(Index.append(rest,tail)),F.and_boolean_left(D.unicode_valid(head),parts_valid(rest),valid_parts),appending_valid_parts_preserves_unicode_validity(rest,tail,F.and_boolean_right(D.unicode_valid(head),parts_valid(rest),valid_parts),valid_tail))

def columns() -> List<&2,D.Column>:
  [D.Column{"id",D.TextValue{},False{}},D.Column{"target",D.TextValue{},False{}},D.Column{"value",D.TextValue{},False{}}]

def schema(table_name: String) -> D.SchemaTable: D.SchemaTable{table_name,"id",columns()}

def fields(row: D.Row) -> List<&2,D.Field>:
  match row:
    case D.Row{key,fields}: fields

law entry_fields_are_exactly_the_supplied_id_target_and_encoded_parts:
  for +key: String
  for +parts: List<&2,String>
  for +target: String
  L.E<{D.row_key(Index.entry(key,parts,target)) == key : String},L.E<{D.find_field(fields(Index.entry(key,parts,target)),"id") == Some{D.VText{key}} : Maybe<&2,D.Value>},L.E<{D.find_field(fields(Index.entry(key,parts,target)),"target") == Some{D.VText{target}} : Maybe<&2,D.Value>},{D.find_field(fields(Index.entry(key,parts,target)),"value") == Some{D.VText{Key.encode(parts)}} : Maybe<&2,D.Value>}>>>
def entry_fields_are_exactly_the_supplied_id_target_and_encoded_parts(key,parts,target): L.Both{{==},L.Both{{==},L.Both{{==},{==}}}}

law unicode_entry_inputs_satisfy_the_exact_required_text_schema:
  for +table_name: String
  for +key: String
  for +parts: List<&2,String>
  for +target: String
  for +valid_key: {D.unicode_valid(key) == True{} : Bool}
  for +valid_parts: {parts_valid(parts) == True{} : Bool}
  for +valid_target: {D.unicode_valid(target) == True{} : Bool}
  {D.row_is_valid(schema(table_name),Index.entry(key,parts,target)) == True{} : Bool}
def unicode_entry_inputs_satisfy_the_exact_required_text_schema(table_name,key,parts,target,valid_key,valid_parts,valid_target):
  F.and_boolean_intro(D.unicode_valid(key) && D.fields_all_valid(columns(),fields(Index.entry(key,parts,target))),D.key_correct(D.find_field(fields(Index.entry(key,parts,target)),"id"),key),F.and_boolean_intro(D.unicode_valid(key),D.fields_all_valid(columns(),fields(Index.entry(key,parts,target))),valid_key,F.and_boolean_intro(D.unicode_valid(key),D.unicode_valid(target) && (D.unicode_valid(Key.encode(parts)) && True{}),valid_key,F.and_boolean_intro(D.unicode_valid(target),D.unicode_valid(Key.encode(parts)) && True{},valid_target,F.and_boolean_intro(D.unicode_valid(Key.encode(parts)),True{},encoding_valid_parts_always_produces_a_valid_unicode_row_key(parts,valid_parts),{==})))),O.string_eq_refl(key))

law valid_unique_entries_always_fit_the_required_index_schema:
  for +table_name: String
  for +parts: List<&2,String>
  for +target: String
  for +valid_parts: {parts_valid(parts) == True{} : Bool}
  for +valid_target: {D.unicode_valid(target) == True{} : Bool}
  {D.row_is_valid(schema(table_name),Index.unique(parts,target)) == True{} : Bool}
def valid_unique_entries_always_fit_the_required_index_schema(table_name,parts,target,valid_parts,valid_target):
  unicode_entry_inputs_satisfy_the_exact_required_text_schema(table_name,Key.encode(parts),parts,target,encoding_valid_parts_always_produces_a_valid_unicode_row_key(parts,valid_parts),valid_parts,valid_target)

law valid_nonunique_entries_always_fit_the_required_index_schema:
  for +table_name: String
  for +parts: List<&2,String>
  for +target: String
  for +valid_parts: {parts_valid(parts) == True{} : Bool}
  for +valid_target: {D.unicode_valid(target) == True{} : Bool}
  {D.row_is_valid(schema(table_name),Index.nonunique(parts,target)) == True{} : Bool}
def valid_nonunique_entries_always_fit_the_required_index_schema(table_name,parts,target,valid_parts,valid_target):
  unicode_entry_inputs_satisfy_the_exact_required_text_schema(table_name,Key.encode(Index.append(parts,[target])),parts,target,encoding_valid_parts_always_produces_a_valid_unicode_row_key(Index.append(parts,[target]),appending_valid_parts_preserves_unicode_validity(parts,[target],valid_parts,F.and_boolean_intro(D.unicode_valid(target),True{},valid_target,{==}))),valid_parts,valid_target)
