# Independent field-index semantics for actual Query.find_field and field.
# Canonical order makes every field name unique, so every original named
# occurrence is returned with its exact value, including present VAbsent.
import Base
import ./RecordCanonicalProofs.bend as C
import ./RecordShapeProofs.bend as Shape
import ./ValueScalarProofs.bend as Scalar
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ./Record.bend as Record
import ./Query.bend as Query
import ../proof/Foundations.bend as F
import ../proof/Orders.bend as O


def at(fields: List<&2,D.Field>,index: Nat) -> Maybe<&2,D.Field>:
  match fields:
    case Nil{}: None{}
    case Con{field,tail}:
      match index:
        case 0n: Some{field}
        case 1n+previous: at(tail,previous)

def field_name(field: D.Field) -> String:
  D.Field{name,value}=field
  name

def field_value(field: D.Field) -> D.Value:
  D.Field{name,value}=field
  value

law present_field_entries_have_exact_name_and_payload_equality:
  for +a: D.Field
  for +b: D.Field
  for same: {Some{a} == Some{b} : Maybe<&2,D.Field>}
  {a == b : D.Field}
def present_field_entries_have_exact_name_and_payload_equality(a,b,same):
  Equal.cong(Maybe<&2,D.Field>,D.Field,result => F.extract_or(D.Field,result,D.Field{"",D.VAbsent{}}),Some{a},Some{b},same)


def Found(+fields: List<&2,D.Field>,+name: String,+value: D.Value) -> Type:
  Exists(Nat,index => {at(fields,index) == Some{D.Field{name,value}} : Maybe<&2,D.Field>})

def FindMeaning(+fields: List<&2,D.Field>,+name: String,result: Maybe<&2,D.Value>) -> Type:
  match result:
    case Some{value}: Found(fields,name,value)
    case None{}: @+index: Nat -> @+value: D.Value -> {at(fields,index) == Some{D.Field{name,value}} : Maybe<&2,D.Field>} -> Empty


def lift_found(+name: String,+head: String,+payload: D.Value,+tail: List<&2,D.Field>,+value: D.Value,found: Found(tail,name,value)) -> Found(Con{D.Field{head,payload},tail},name,value):
  match found:
    case Tuple{index,present}: Tuple{1n+index,present}


def no_head_or_tail(+name: String,+head: String,+payload: D.Value,+tail: List<&2,D.Field>,index: Nat,+value: D.Value,present: {at(Con{D.Field{head,payload},tail},index) == Some{D.Field{name,value}} : Maybe<&2,D.Field>},different: {String.eq(head,name) == False{} : Bool},tail_absent: @+index: Nat -> @+value: D.Value -> {at(tail,index) == Some{D.Field{name,value}} : Maybe<&2,D.Field>} -> Empty) -> Empty:
  match index:
    case 0n:
      F.false_negative_true(Equal.trans(Bool,False{},String.eq(head,name),True{},Equal.sym(Bool,String.eq(head,name),False{},different),
        Equal.trans(Bool,String.eq(head,name),String.eq(name,name),True{},Equal.cong(String,Bool,k => String.eq(k,name),head,name,Equal.cong(D.Field,String,field_name,D.Field{head,payload},D.Field{name,value},present_field_entries_have_exact_name_and_payload_equality(D.Field{head,payload},D.Field{name,value},present))),O.string_eq_refl(name))))
    case 1n+previous: tail_absent(previous,value,present)


def find_step(equal: Bool,+name: String,+head: String,+payload: D.Value,+tail: List<&2,D.Field>,+actual: {String.eq(head,name) == equal : Bool},result: Maybe<&2,D.Value>,correct: FindMeaning(tail,name,result)) -> FindMeaning(Con{D.Field{head,payload},tail},name,Bool.pick(Maybe<&2,D.Value>,equal,Some{payload},result)):
  match equal result:
    case True{} result: Tuple{0n,Equal.cong(String,Maybe<&2,D.Field>,key => Some{D.Field{key,payload}},head,name,O.string_equal(head,name,actual))}
    case False{} Some{+value}: lift_found(name,head,payload,tail,value,correct)
    case False{} None{}: +index => +value => present => no_head_or_tail(name,head,payload,tail,index,value,present,actual,correct)

law actual_raw_record_lookup_has_exact_source_field_or_complete_absence:
  for +fields: List<&2,D.Field>
  for +name: String
  FindMeaning(fields,name,Query.find_field(Record.raw(fields),name))
def actual_raw_record_lookup_has_exact_source_field_or_complete_absence(fields,name):
  match fields:
    case Nil{}: +index => +value => present => F.none_negative_some(D.Field,D.Field{name,value},present)
    case Con{D.Field{+head,+payload},+tail}: find_step(String.eq(head,name),name,head,payload,tail,{==},Query.find_field(Record.raw(tail),name),actual_raw_record_lookup_has_exact_source_field_or_complete_absence(tail,name))

law all_later_names_differ_from_each_indexed_field_name:
  for +previous: String
  for +fields: List<&2,D.Field>
  for +index: Nat
  for +name: String
  for +value: D.Value
  for +present: {at(fields,index) == Some{D.Field{name,value}} : Maybe<&2,D.Field>}
  for later: C.Later(previous,fields)
  {String.eq(previous,name) == False{} : Bool}
def all_later_names_differ_from_each_indexed_field_name(previous,fields,index,name,value,present,later):
  match fields index later:
    case Nil{} index Unit{}: L.ex_false({String.eq(previous,name) == False{} : Bool},F.none_negative_some(D.Field,D.Field{name,value},present))
    case Con{D.Field{+head,+payload},+tail} 0n Scalar.Both{ordered,rest}:
      %Equal.cong(D.Field,String,field_name,D.Field{head,payload},D.Field{name,value},present_field_entries_have_exact_name_and_payload_equality(D.Field{head,payload},D.Field{name,value},present)) : {String.eq(previous,_) == False{} : Bool}
      O.string_lt_neq(previous,head,ordered)
    case Con{D.Field{head,payload},+tail} 1n+previous_index Scalar.Both{ordered,rest}: all_later_names_differ_from_each_indexed_field_name(previous,tail,previous_index,name,value,present,rest)

law every_original_canonical_field_is_returned_with_its_exact_value:
  for +fields: List<&2,D.Field>
  for +name: String
  for +index: Nat
  for +value: D.Value
  for +canonical: C.Canonical(fields)
  for +present: {at(fields,index) == Some{D.Field{name,value}} : Maybe<&2,D.Field>}
  {Query.find_field(Record.raw(fields),name) == Some{value} : Maybe<&2,D.Value>}
def every_original_canonical_field_is_returned_with_its_exact_value(fields,name,index,value,canonical,present):
  match fields index canonical:
    case Nil{} index Unit{}: L.ex_false({None{} == Some{value} : Maybe<&2,D.Value>},F.none_negative_some(D.Field,D.Field{name,value},present))
    case Con{D.Field{+head,+payload},+tail} 0n Scalar.Both{valid_name,Scalar.Both{valid_value,Scalar.Both{later,rest}}}:
      +same = present_field_entries_have_exact_name_and_payload_equality(D.Field{head,payload},D.Field{name,value},present)
      Equal.trans(Maybe<&2,D.Value>,Query.find_field(Record.raw(Con{D.Field{head,payload},tail}),name),Some{payload},Some{value},
        Equal.cong(Bool,Maybe<&2,D.Value>,equal => Bool.pick(Maybe<&2,D.Value>,equal,Some{payload},Query.find_field(Record.raw(tail),name)),String.eq(head,name),True{},
          Equal.trans(Bool,String.eq(head,name),String.eq(name,name),True{},Equal.cong(String,Bool,key => String.eq(key,name),head,name,Equal.cong(D.Field,String,field_name,D.Field{head,payload},D.Field{name,value},same)),O.string_eq_refl(name))),
        Equal.cong(D.Value,Maybe<&2,D.Value>,item => Some{item},payload,value,Equal.cong(D.Field,D.Value,field_value,D.Field{head,payload},D.Field{name,value},same)))
    case Con{D.Field{+head,+payload},+tail} 1n+previous Scalar.Both{valid_name,Scalar.Both{valid_value,Scalar.Both{later,rest}}}:
      Equal.trans(Maybe<&2,D.Value>,Query.find_field(Record.raw(Con{D.Field{head,payload},tail}),name),Query.find_field(Record.raw(tail),name),Some{value},
        Equal.cong(Bool,Maybe<&2,D.Value>,equal => Bool.pick(Maybe<&2,D.Value>,equal,Some{payload},Query.find_field(Record.raw(tail),name)),String.eq(head,name),False{},all_later_names_differ_from_each_indexed_field_name(head,tail,previous,name,value,present,later)),every_original_canonical_field_is_returned_with_its_exact_value(tail,name,previous,value,rest,present))


def Meaning(+fields: List<&2,D.Field>,+name: String,result: Maybe<&2,D.Value>) -> Type:
  match result:
    case Some{value}: L.E<C.Canonical(fields),Found(fields,name,value)>
    case None{}: C.Canonical(fields) -> @+index: Nat -> @+value: D.Value -> {at(fields,index) == Some{D.Field{name,value}} : Maybe<&2,D.Field>} -> Empty

def accepted_find_result(+fields: List<&2,D.Field>,+name: String,valid: {D.value_valid(Record.raw(fields)) == True{} : Bool},result: Maybe<&2,D.Value>,correct: FindMeaning(fields,name,result)) -> Meaning(fields,name,result):
  match result:
    case Some{value}: L.Both{C.every_valid_record_encoding_has_canonical_fields(fields,valid),correct}
    case None{}: canonical => +index => +value => present => correct(index,value,present)

def validated_result_case(valid: Bool,+fields: List<&2,D.Field>,+name: String,+actual: {D.value_valid(Record.raw(fields)) == valid : Bool}) -> Meaning(fields,name,Query.field_valid(valid,Record.raw(fields),name)):
  match valid:
    case False{}: canonical => +index => +value => present => F.false_negative_true(Equal.trans(Bool,False{},D.value_valid(Record.raw(fields)),True{},Equal.sym(Bool,D.value_valid(Record.raw(fields)),False{},actual),C.every_canonical_field_list_has_a_valid_record_encoding(fields,canonical)))
    case True{}: accepted_find_result(fields,name,actual,Query.find_field(Record.raw(fields),name),actual_raw_record_lookup_has_exact_source_field_or_complete_absence(fields,name))

law actual_validated_field_lookup_has_exact_canonical_source_or_complete_rejection:
  for +fields: List<&2,D.Field>
  for +name: String
  Meaning(fields,name,Query.field(Record.raw(fields),name))
def actual_validated_field_lookup_has_exact_canonical_source_or_complete_rejection(fields,name):
  validated_result_case(D.value_valid(Record.raw(fields)),fields,name,{==})

law every_original_canonical_field_is_accepted_with_its_exact_value:
  for +fields: List<&2,D.Field>
  for +name: String
  for +index: Nat
  for +value: D.Value
  for +canonical: C.Canonical(fields)
  for +present: {at(fields,index) == Some{D.Field{name,value}} : Maybe<&2,D.Field>}
  {Query.field(Record.raw(fields),name) == Some{value} : Maybe<&2,D.Value>}
def every_original_canonical_field_is_accepted_with_its_exact_value(fields,name,index,value,canonical,present):
  Equal.trans(Maybe<&2,D.Value>,Query.field(Record.raw(fields),name),Query.find_field(Record.raw(fields),name),Some{value},
    Equal.cong(Bool,Maybe<&2,D.Value>,valid => Query.field_valid(valid,Record.raw(fields),name),D.value_valid(Record.raw(fields)),True{},C.every_canonical_field_list_has_a_valid_record_encoding(fields,canonical)),
    every_original_canonical_field_is_returned_with_its_exact_value(fields,name,index,value,canonical,present))

law all_equal_named_canonical_source_fields_have_the_exact_same_value:
  for +fields: List<&2,D.Field>
  for +name: String
  for +i: Nat
  for +j: Nat
  for +a: D.Value
  for +b: D.Value
  for +canonical: C.Canonical(fields)
  for first: {at(fields,i) == Some{D.Field{name,a}} : Maybe<&2,D.Field>}
  for second: {at(fields,j) == Some{D.Field{name,b}} : Maybe<&2,D.Field>}
  {a == b : D.Value}
def all_equal_named_canonical_source_fields_have_the_exact_same_value(fields,name,i,j,a,b,canonical,first,second):
  Equal.cong(Maybe<&2,D.Value>,D.Value,result => F.extract_or(D.Value,result,D.VAbsent{}),Some{a},Some{b},
    Equal.trans(Maybe<&2,D.Value>,Some{a},Query.find_field(Record.raw(fields),name),Some{b},Equal.sym(Maybe<&2,D.Value>,Query.find_field(Record.raw(fields),name),Some{a},every_original_canonical_field_is_returned_with_its_exact_value(fields,name,i,a,canonical,first)),every_original_canonical_field_is_returned_with_its_exact_value(fields,name,j,b,canonical,second)))

law every_original_field_of_any_valid_record_is_accepted_exactly:
  for +input: D.Value
  for +name: String
  for +index: Nat
  for +value: D.Value
  for +record: {D.is_record(input) == True{} : Bool}
  for +valid: {D.value_valid(input) == True{} : Bool}
  for present: {at(Record.fields(input),index) == Some{D.Field{name,value}} : Maybe<&2,D.Field>}
  {Query.field(input,name) == Some{value} : Maybe<&2,D.Value>}
def every_original_field_of_any_valid_record_is_accepted_exactly(input,name,index,value,record,valid,present):
  Equal.trans(Maybe<&2,D.Value>,Query.field(input,name),Query.field(Record.raw(Record.fields(input)),name),Some{value},
    Equal.sym(Maybe<&2,D.Value>,Query.field(Record.raw(Record.fields(input)),name),Query.field(input,name),Equal.cong(D.Value,Maybe<&2,D.Value>,record_value => Query.field(record_value,name),Record.raw(Record.fields(input)),input,Shape.unchecked_fields_reverse_roundtrip_preserves_exactly_the_proper_record_shape_domain(input,Shape.every_contract_valid_record_has_proper_record_tail_shape(input,record,valid)))),
    every_original_canonical_field_is_accepted_with_its_exact_value(Record.fields(input),name,index,value,Shape.every_contract_valid_record_exposes_exact_canonical_original_fields(input,record,valid),present))


def indexed_head_has_the_query_name(+head: String,+payload: D.Value,+name: String,+value: D.Value,present: {Some{D.Field{head,payload}} == Some{D.Field{name,value}} : Maybe<&2,D.Field>}) -> {String.eq(head,name) == True{} : Bool}:
  Equal.trans(Bool,String.eq(head,name),String.eq(name,name),True{},Equal.cong(String,Bool,key => String.eq(key,name),head,name,Equal.cong(D.Field,String,field_name,D.Field{head,payload},D.Field{name,value},present_field_entries_have_exact_name_and_payload_equality(D.Field{head,payload},D.Field{name,value},present))),O.string_eq_refl(name))

law canonical_field_names_have_unique_original_source_indices:
  for +fields: List<&2,D.Field>
  for +name: String
  for +i: Nat
  for +j: Nat
  for +a: D.Value
  for +b: D.Value
  for canonical: C.Canonical(fields)
  for first: {at(fields,i) == Some{D.Field{name,a}} : Maybe<&2,D.Field>}
  for second: {at(fields,j) == Some{D.Field{name,b}} : Maybe<&2,D.Field>}
  {i == j : Nat}
def canonical_field_names_have_unique_original_source_indices(fields,name,i,j,a,b,canonical,first,second):
  match fields i j canonical:
    case Nil{} i j Unit{}: L.ex_false({i == j : Nat},F.none_negative_some(D.Field,D.Field{name,a},first))
    case Con{D.Field{head,payload},tail} 0n 0n Scalar.Both{valid_name,Scalar.Both{valid_value,Scalar.Both{later,rest}}}: {==}
    case Con{D.Field{+head,+payload},+tail} 0n 1n+previous Scalar.Both{valid_name,Scalar.Both{valid_value,Scalar.Both{later,rest}}}:
      F.absurd_boolean({0n == 1n+previous : Nat},Equal.trans(Bool,False{},String.eq(head,name),True{},Equal.sym(Bool,String.eq(head,name),False{},all_later_names_differ_from_each_indexed_field_name(head,tail,previous,name,b,second,later)),indexed_head_has_the_query_name(head,payload,name,a,first)))
    case Con{D.Field{+head,+payload},+tail} 1n+previous 0n Scalar.Both{valid_name,Scalar.Both{valid_value,Scalar.Both{later,rest}}}:
      F.absurd_boolean({1n+previous == 0n : Nat},Equal.trans(Bool,False{},String.eq(head,name),True{},Equal.sym(Bool,String.eq(head,name),False{},all_later_names_differ_from_each_indexed_field_name(head,tail,previous,name,a,first,later)),indexed_head_has_the_query_name(head,payload,name,b,second)))
    case Con{D.Field{head,payload},+tail} 1n+previous 1n+later_index Scalar.Both{valid_name,Scalar.Both{valid_value,Scalar.Both{later,rest}}}: Equal.cong(Nat,Nat,index => 1n+index,previous,later_index,canonical_field_names_have_unique_original_source_indices(tail,name,previous,later_index,a,b,rest,first,second))
