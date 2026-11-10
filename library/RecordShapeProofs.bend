# Record.fields is unchecked: reverse re-encoding is guaranteed on proper
# record TAIL SHAPES only. Malformed tails are not claimed to roundtrip.
# Canonical valid records have that shape; arbitrary nested payloads need not.
import Base
import ./RecordCanonicalProofs.bend as Canonical
import ../contract/Data.bend as D
import ./Record.bend as Record
import ../proof/Foundations.bend as F


def Shape(input: D.Value) -> Data:
  match input:
    case D.VRecordEmpty{}: Unit
    case D.VRecord{name,value,tail}: Shape(tail)
    case _: {False{} == True{} : Bool}

law every_raw_field_list_has_proper_record_tail_shape:
  for +fields: List<&2,D.Field>
  Shape(Record.raw(fields))
def every_raw_field_list_has_proper_record_tail_shape(fields):
  match fields:
    case Nil{}: Unit{}
    case Con{D.Field{name,value},tail}: every_raw_field_list_has_proper_record_tail_shape(tail)

law unchecked_fields_reverse_roundtrip_preserves_exactly_the_proper_record_shape_domain:
  for +input: D.Value
  for shape: Shape(input)
  {Record.raw(Record.fields(input)) == input : D.Value}
def unchecked_fields_reverse_roundtrip_preserves_exactly_the_proper_record_shape_domain(input,shape):
  match input:
    case D.VRecordEmpty{}: {==}
    case D.VRecord{+name,+value,+tail}: Equal.cong(D.Value,D.Value,rest => D.VRecord{name,value,rest},Record.raw(Record.fields(tail)),tail,unchecked_fields_reverse_roundtrip_preserves_exactly_the_proper_record_shape_domain(tail,shape))
    case D.VAbsent{}: F.absurd_boolean({D.VRecordEmpty{} == D.VAbsent{} : D.Value},shape)
    case D.VBool{b}: F.absurd_boolean({D.VRecordEmpty{} == D.VBool{b} : D.Value},shape)
    case D.VInt{h,l}: F.absurd_boolean({D.VRecordEmpty{} == D.VInt{h,l} : D.Value},shape)
    case D.VText{s}: F.absurd_boolean({D.VRecordEmpty{} == D.VText{s} : D.Value},shape)
    case D.VListEmpty{}: F.absurd_boolean({D.VRecordEmpty{} == D.VListEmpty{} : D.Value},shape)
    case D.VList{h,t}: F.absurd_boolean({D.VRecordEmpty{} == D.VList{h,t} : D.Value},shape)

law a_valid_ordered_record_tail_has_record_constructor_shape:
  for +tail: D.Value
  for +previous: String
  for ordered: {D.record_later(tail,previous) == True{} : Bool}
  {D.is_record(tail) == True{} : Bool}
def a_valid_ordered_record_tail_has_record_constructor_shape(tail,previous,ordered):
  match tail:
    case D.VRecordEmpty{}: {==}
    case D.VRecord{name,value,rest}: {==}
    case D.VAbsent{}: F.absurd_boolean({False{} == True{} : Bool},ordered)
    case D.VBool{b}: F.absurd_boolean({False{} == True{} : Bool},ordered)
    case D.VInt{h,l}: F.absurd_boolean({False{} == True{} : Bool},ordered)
    case D.VText{s}: F.absurd_boolean({False{} == True{} : Bool},ordered)
    case D.VListEmpty{}: F.absurd_boolean({False{} == True{} : Bool},ordered)
    case D.VList{h,t}: F.absurd_boolean({False{} == True{} : Bool},ordered)

law every_contract_valid_record_has_proper_record_tail_shape:
  for +input: D.Value
  for record: {D.is_record(input) == True{} : Bool}
  for +valid: {D.value_valid(input) == True{} : Bool}
  Shape(input)
def every_contract_valid_record_has_proper_record_tail_shape(input,record,valid):
  match input:
    case D.VRecordEmpty{}: Unit{}
    case D.VRecord{+name,+value,+tail}:
      every_contract_valid_record_has_proper_record_tail_shape(tail,
        a_valid_ordered_record_tail_has_record_constructor_shape(tail,name,F.and_boolean_right(D.name_valid(name) && D.value_valid(value),D.record_later(tail,name),F.and_boolean_left(D.name_valid(name) && D.value_valid(value) && D.record_later(tail,name),D.value_valid(tail),valid))),
        F.and_boolean_right(D.name_valid(name) && D.value_valid(value) && D.record_later(tail,name),D.value_valid(tail),valid))
    case D.VAbsent{}: F.absurd_boolean(Shape(D.VAbsent{}),record)
    case D.VBool{b}: F.absurd_boolean(Shape(D.VBool{b}),record)
    case D.VInt{h,l}: F.absurd_boolean(Shape(D.VInt{h,l}),record)
    case D.VText{s}: F.absurd_boolean(Shape(D.VText{s}),record)
    case D.VListEmpty{}: F.absurd_boolean(Shape(D.VListEmpty{}),record)
    case D.VList{h,t}: F.absurd_boolean(Shape(D.VList{h,t}),record)

law every_contract_valid_record_exposes_exact_canonical_original_fields:
  for +input: D.Value
  for record: {D.is_record(input) == True{} : Bool}
  for +valid: {D.value_valid(input) == True{} : Bool}
  Canonical.Canonical(Record.fields(input))
def every_contract_valid_record_exposes_exact_canonical_original_fields(input,record,valid):
  Canonical.every_valid_record_encoding_has_canonical_fields(Record.fields(input),
    Equal.trans(Bool,D.value_valid(Record.raw(Record.fields(input))),D.value_valid(input),True{},Equal.cong(D.Value,Bool,D.value_valid,Record.raw(Record.fields(input)),input,unchecked_fields_reverse_roundtrip_preserves_exactly_the_proper_record_shape_domain(input,every_contract_valid_record_has_proper_record_tail_shape(input,record,valid))),valid))

law reverse_reencoding_equality_requires_proper_record_tail_shape:
  for +input: D.Value
  for same: {Record.raw(Record.fields(input)) == input : D.Value}
  Shape(input)
def reverse_reencoding_equality_requires_proper_record_tail_shape(input,same):
  %same : Shape(_)
  every_raw_field_list_has_proper_record_tail_shape(Record.fields(input))
