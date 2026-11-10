# Canonical fields mean every name/value is contract-valid and EVERY earlier
# field name is strictly before every later one. This implies unique names;
# construction never sorts, drops duplicates, or changes payloads.
import Base
import ./ValueScalarProofs.bend as Scalar
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ./Record.bend as Record
import ../proof/Foundations.bend as F
import ../proof/Orders.bend as O

def Later(+previous: String,fields: List<&2,D.Field>) -> Data:
  match fields:
    case Nil{}: Unit
    case Con{D.Field{name,value},tail}: Scalar.Both<{String.is_lt(previous,name) == True{} : Bool},Later(previous,tail)>

def Canonical(fields: List<&2,D.Field>) -> Data:
  match fields:
    case Nil{}: Unit
    case Con{D.Field{+name,value},+tail}: Scalar.Both<{D.name_valid(name) == True{} : Bool},Scalar.Both<{D.value_valid(value) == True{} : Bool},Scalar.Both<Later(name,tail),Canonical(tail)>>>

def later_transitive(+first: String,+second: String,+fields: List<&2,D.Field>,+ordered: {String.is_lt(first,second) == True{} : Bool},later: Later(second,fields)) -> Later(first,fields):
  match fields later:
    case Nil{} Unit{}: Unit{}
    case Con{D.Field{+name,value},+tail} Scalar.Both{head,rest}: Scalar.Both{O.string_lt_trans(first,second,name,ordered,head),later_transitive(first,second,tail,ordered,rest)}

law all_pair_field_order_implies_the_immediate_contract_order:
  for +previous: String
  for +fields: List<&2,D.Field>
  for later: Later(previous,fields)
  {D.record_later(Record.raw(fields),previous) == True{} : Bool}
def all_pair_field_order_implies_the_immediate_contract_order(previous,fields,later):
  match fields later:
    case Nil{} Unit{}: {==}
    case Con{D.Field{name,value},tail} Scalar.Both{first,rest}: first

law immediate_order_plus_canonical_tail_implies_all_pair_order:
  for +previous: String
  for +fields: List<&2,D.Field>
  for +immediate: {D.record_later(Record.raw(fields),previous) == True{} : Bool}
  for canonical: Canonical(fields)
  Later(previous,fields)
def immediate_order_plus_canonical_tail_implies_all_pair_order(previous,fields,immediate,canonical):
  match fields canonical:
    case Nil{} Unit{}: Unit{}
    case Con{D.Field{+name,value},+tail} Scalar.Both{valid_name,Scalar.Both{valid_value,Scalar.Both{later,rest}}}: Scalar.Both{immediate,later_transitive(previous,name,tail,immediate,later)}

law every_canonical_field_list_has_a_valid_record_encoding:
  for +fields: List<&2,D.Field>
  for canonical: Canonical(fields)
  {D.value_valid(Record.raw(fields)) == True{} : Bool}
def every_canonical_field_list_has_a_valid_record_encoding(fields,canonical):
  match fields canonical:
    case Nil{} Unit{}: {==}
    case Con{D.Field{+name,+value},+tail} Scalar.Both{valid_name,Scalar.Both{valid_value,Scalar.Both{later,rest}}}:
      F.and_boolean_intro(D.name_valid(name) && D.value_valid(value) && D.record_later(Record.raw(tail),name),D.value_valid(Record.raw(tail)),
        F.and_boolean_intro(D.name_valid(name) && D.value_valid(value),D.record_later(Record.raw(tail),name),F.and_boolean_intro(D.name_valid(name),D.value_valid(value),valid_name,valid_value),all_pair_field_order_implies_the_immediate_contract_order(name,tail,later)),every_canonical_field_list_has_a_valid_record_encoding(tail,rest))

law every_valid_record_encoding_has_canonical_fields:
  for +fields: List<&2,D.Field>
  for +valid: {D.value_valid(Record.raw(fields)) == True{} : Bool}
  Canonical(fields)
def every_valid_record_encoding_has_canonical_fields(fields,valid):
  match fields:
    case Nil{}: Unit{}
    case Con{D.Field{+name,+value},+tail}:
      +head = F.and_boolean_left(D.name_valid(name) && D.value_valid(value) && D.record_later(Record.raw(tail),name),D.value_valid(Record.raw(tail)),valid)
      +named_value = F.and_boolean_left(D.name_valid(name) && D.value_valid(value),D.record_later(Record.raw(tail),name),head)
      +tail_canonical = every_valid_record_encoding_has_canonical_fields(tail,F.and_boolean_right(D.name_valid(name) && D.value_valid(value) && D.record_later(Record.raw(tail),name),D.value_valid(Record.raw(tail)),valid))
      Scalar.Both{F.and_boolean_left(D.name_valid(name),D.value_valid(value),named_value),Scalar.Both{F.and_boolean_right(D.name_valid(name),D.value_valid(value),named_value),Scalar.Both{
        immediate_order_plus_canonical_tail_implies_all_pair_order(name,tail,F.and_boolean_right(D.name_valid(name) && D.value_valid(value),D.record_later(Record.raw(tail),name),head),tail_canonical),tail_canonical}}}


def Meaning(+fields: List<&2,D.Field>,result: Maybe<&2,D.Value>) -> Type:
  match result:
    case Some{record}: L.E<{record == Record.raw(fields) : D.Value},L.E<Canonical(fields),{Record.fields(record) == fields : List<&2,D.Field>}>>
    case None{}: Canonical(fields) -> Empty

def checked_case(valid: Bool,+fields: List<&2,D.Field>,actual: {D.value_valid(Record.raw(fields)) == valid : Bool}) -> Meaning(fields,Bool.pick(Maybe<&2,D.Value>,valid,Some{Record.raw(fields)},None{})):
  match valid:
    case True{}: L.Both{{==},L.Both{every_valid_record_encoding_has_canonical_fields(fields,actual),Record.fields_roundtrip(fields)}}
    case False{}: canonical => F.false_negative_true(Equal.trans(Bool,False{},D.value_valid(Record.raw(fields)),True{},Equal.sym(Bool,D.value_valid(Record.raw(fields)),False{},actual),every_canonical_field_list_has_a_valid_record_encoding(fields,canonical)))

law actual_record_make_accepts_exactly_canonical_field_lists_without_changing_them:
  for +fields: List<&2,D.Field>
  Meaning(fields,Record.make(fields))
def actual_record_make_accepts_exactly_canonical_field_lists_without_changing_them(fields):
  checked_case(D.value_valid(Record.raw(fields)),fields,{==})

law canonical_fields_are_accepted_with_the_exact_original_record_payload:
  for +fields: List<&2,D.Field>
  for canonical: Canonical(fields)
  {Record.make(fields) == Some{Record.raw(fields)} : Maybe<&2,D.Value>}
def canonical_fields_are_accepted_with_the_exact_original_record_payload(fields,canonical):
  Equal.cong(Bool,Maybe<&2,D.Value>,valid => Bool.pick(Maybe<&2,D.Value>,valid,Some{Record.raw(fields)},None{}),D.value_valid(Record.raw(fields)),True{},every_canonical_field_list_has_a_valid_record_encoding(fields,canonical))
