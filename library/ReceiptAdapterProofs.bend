# Exact Return meaning and literal binding semantics for the reusable receipt
# helpers. These statements concern every constructor, including malformed
# nested values; they neither grant policy nor assume a completed transaction.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Logic.bend as L
import ./Receipts.bend as H
import ../proof/Foundations.bend as F
import ../proof/Orders.bend as O

def row_absent(r: S.Return) -> Bool:
  match r:
    case S.Datum{D.RowAbsent{}}: True{}
    case _: False{}
def text_cell(r: S.Return) -> Bool:
  match r:
    case S.Datum{D.Cell{D.VText{value}}}: True{}
    case _: False{}

def Meaning(+r: S.Return,value: H.Lookup) -> Type:
  match value:
    case H.Missing{}: {r == S.Datum{D.RowAbsent{}} : S.Return}
    case H.StoredText{text}: {r == S.Datum{D.Cell{D.VText{text}}} : S.Return}
    case H.Unexpected{}: L.E<({r == S.Datum{D.RowAbsent{}} : S.Return} -> Empty),(@+text: String -> {r == S.Datum{D.Cell{D.VText{text}}} : S.Return} -> Empty)>

def excludes_missing(+r: S.Return,negative: {row_absent(r) == False{} : Bool},same: {r == S.Datum{D.RowAbsent{}} : S.Return}) -> Empty:
  F.false_negative_true(Equal.trans(Bool,False{},row_absent(r),True{},Equal.sym(Bool,row_absent(r),False{},negative),Equal.cong(S.Return,Bool,row_absent,r,S.Datum{D.RowAbsent{}},same)))
def excludes_text(+r: S.Return,negative: {text_cell(r) == False{} : Bool},+text: String,same: {r == S.Datum{D.Cell{D.VText{text}}} : S.Return}) -> Empty:
  F.false_negative_true(Equal.trans(Bool,False{},text_cell(r),True{},Equal.sym(Bool,text_cell(r),False{},negative),Equal.cong(S.Return,Bool,text_cell,r,S.Datum{D.Cell{D.VText{text}}},same)))
def not_classified(+r: S.Return,missing: {row_absent(r) == False{} : Bool},text: {text_cell(r) == False{} : Bool}) -> Meaning(r,H.Unexpected{}):
  L.Both{same => excludes_missing(r,missing,same),value => same => excludes_text(r,text,value,same)}

law actual_receipt_decoder_has_exact_missing_text_or_exhaustive_rejection_meaning:
  for +r: S.Return
  Meaning(r,H.observed(r))
def actual_receipt_decoder_has_exact_missing_text_or_exhaustive_rejection_meaning(r):
  match r:
    case S.UnitValue{}: not_classified(S.UnitValue{},{==},{==})
    case S.Datum{D.RowAbsent{}}: {==}
    case S.Datum{D.Keys{keys}}: not_classified(S.Datum{D.Keys{keys}},{==},{==})
    case S.Datum{D.Count{count}}: not_classified(S.Datum{D.Count{count}},{==},{==})
    case S.Datum{D.Existence{exists}}: not_classified(S.Datum{D.Existence{exists}},{==},{==})
    case S.Datum{D.Cell{D.VText{text}}}: {==}
    case S.Datum{D.Cell{D.VAbsent{}}}: not_classified(S.Datum{D.Cell{D.VAbsent{}}},{==},{==})
    case S.Datum{D.Cell{D.VBool{value}}}: not_classified(S.Datum{D.Cell{D.VBool{value}}},{==},{==})
    case S.Datum{D.Cell{D.VInt{high,low}}}: not_classified(S.Datum{D.Cell{D.VInt{high,low}}},{==},{==})
    case S.Datum{D.Cell{D.VListEmpty{}}}: not_classified(S.Datum{D.Cell{D.VListEmpty{}}},{==},{==})
    case S.Datum{D.Cell{D.VList{head,tail}}}: not_classified(S.Datum{D.Cell{D.VList{head,tail}}},{==},{==})
    case S.Datum{D.Cell{D.VRecordEmpty{}}}: not_classified(S.Datum{D.Cell{D.VRecordEmpty{}}},{==},{==})
    case S.Datum{D.Cell{D.VRecord{name,value,tail}}}: not_classified(S.Datum{D.Cell{D.VRecord{name,value,tail}}},{==},{==})

law receipt_binding_matches_only_exact_literal_operation_and_input:
  for +operation: String
  for +input: String
  for +stored_operation: String
  for +stored_input: String
  for +same: {H.matches(operation,input,stored_operation,stored_input) == True{} : Bool}
  L.E<{operation == stored_operation : String},{input == stored_input : String}>
def receipt_binding_matches_only_exact_literal_operation_and_input(operation,input,stored_operation,stored_input,same):
  L.Both{O.string_equal(operation,stored_operation,F.and_boolean_left(String.eq(operation,stored_operation),String.eq(input,stored_input),same)),O.string_equal(input,stored_input,F.and_boolean_right(String.eq(operation,stored_operation),String.eq(input,stored_input),same))}

law equal_literal_operation_and_input_always_match_the_binding:
  for +operation: String
  for +input: String
  for +stored_operation: String
  for +stored_input: String
  for same_operation: {operation == stored_operation : String}
  for same_input: {input == stored_input : String}
  {H.matches(operation,input,stored_operation,stored_input) == True{} : Bool}
def equal_literal_operation_and_input_always_match_the_binding(operation,input,stored_operation,stored_input,same_operation,same_input):
  F.and_boolean_intro(String.eq(operation,stored_operation),String.eq(input,stored_input),Equal.trans(Bool,String.eq(operation,stored_operation),String.eq(stored_operation,stored_operation),True{},Equal.cong(String,Bool,value => String.eq(value,stored_operation),operation,stored_operation,same_operation),O.string_eq_refl(stored_operation)),Equal.trans(Bool,String.eq(input,stored_input),String.eq(stored_input,stored_input),True{},Equal.cong(String,Bool,value => String.eq(value,stored_input),input,stored_input,same_input),O.string_eq_refl(stored_input)))

law a_false_binding_refutes_simultaneous_literal_equality:
  for +operation: String
  for +input: String
  for +stored_operation: String
  for +stored_input: String
  for different: {H.matches(operation,input,stored_operation,stored_input) == False{} : Bool}
  for same: L.E<{operation == stored_operation : String},{input == stored_input : String}>
  Empty
def a_false_binding_refutes_simultaneous_literal_equality(operation,input,stored_operation,stored_input,different,same):
  match same:
    case L.Both{op,value}: F.false_negative_true(Equal.trans(Bool,False{},H.matches(operation,input,stored_operation,stored_input),True{},Equal.sym(Bool,H.matches(operation,input,stored_operation,stored_input),False{},different),equal_literal_operation_and_input_always_match_the_binding(operation,input,stored_operation,stored_input,op,value)))

law the_receipt_write_unit_return_hands_off_to_the_exact_caller:
  for -next: S.Action
  {H.written(next,S.UnitValue{}) == next : S.Action}
def the_receipt_write_unit_return_hands_off_to_the_exact_caller(next): {==}
law every_receipt_write_datum_refuses_without_handing_off:
  for -next: S.Action
  for +observation: D.Observation
  {H.written(next,S.Datum{observation}) == S.Refuse{D.VText{"unexpected write return"}} : S.Action}
def every_receipt_write_datum_refuses_without_handing_off(next,observation): {==}

# This domain is about a supplied FIELD VALUE, independently of helper output.
def NonText(value: D.Value) -> Data:
  match value:
    case D.VText{text}: {False{} == True{} : Bool}
    case _: Unit

law a_nontext_field_has_the_unexpected_receipt_decoder_class:
  for +value: D.Value
  for invalid: NonText(value)
  {H.observed(S.Datum{D.Cell{value}}) == H.Unexpected{} : H.Lookup}
def a_nontext_field_has_the_unexpected_receipt_decoder_class(value,invalid):
  match value:
    case D.VText{text}: F.absurd_boolean({H.observed(S.Datum{D.Cell{D.VText{text}}}) == H.Unexpected{} : H.Lookup},invalid)
    case D.VAbsent{}: {==}
    case D.VBool{value}: {==}
    case D.VInt{high,low}: {==}
    case D.VListEmpty{}: {==}
    case D.VList{head,tail}: {==}
    case D.VRecordEmpty{}: {==}
    case D.VRecord{name,value,tail}: {==}

law a_nontext_input_return_refuses_before_its_miss_or_result_caller:
  for +owner: String
  for +key: String
  for +operation: String
  for +input: String
  for -missing: S.Action
  for -done: S.Return -> S.Action
  for +value: D.Value
  for invalid: NonText(value)
  {H.input_seen(owner,key,operation,input,missing,done,S.Datum{D.Cell{value}}) == S.Refuse{D.VText{"invalid receipt"}} : S.Action}
def a_nontext_input_return_refuses_before_its_miss_or_result_caller(owner,key,operation,input,missing,done,value,invalid):
  Equal.cong(H.Lookup,S.Action,kind => H.input_value(owner,key,operation,input,missing,done,kind),H.observed(S.Datum{D.Cell{value}}),H.Unexpected{},a_nontext_field_has_the_unexpected_receipt_decoder_class(value,invalid))

law a_nontext_operation_return_refuses_before_its_result_caller:
  for +owner: String
  for +key: String
  for +operation: String
  for -done: S.Return -> S.Action
  for +value: D.Value
  for invalid: NonText(value)
  {H.operation_seen(owner,key,operation,done,S.Datum{D.Cell{value}}) == S.Refuse{D.VText{"invalid receipt"}} : S.Action}
def a_nontext_operation_return_refuses_before_its_result_caller(owner,key,operation,done,value,invalid):
  Equal.cong(H.Lookup,S.Action,kind => H.operation_value(owner,key,operation,done,kind),H.observed(S.Datum{D.Cell{value}}),H.Unexpected{},a_nontext_field_has_the_unexpected_receipt_decoder_class(value,invalid))

law only_the_initial_input_row_absence_hands_off_to_the_miss_caller:
  for +owner: String
  for +key: String
  for +operation: String
  for +input: String
  for -missing: S.Action
  for -done: S.Return -> S.Action
  {H.input_seen(owner,key,operation,input,missing,done,S.Datum{D.RowAbsent{}}) == missing : S.Action}
def only_the_initial_input_row_absence_hands_off_to_the_miss_caller(owner,key,operation,input,missing,done): {==}

law row_absence_during_the_operation_read_is_an_invalid_receipt:
  for +owner: String
  for +key: String
  for +operation: String
  for -done: S.Return -> S.Action
  {H.operation_seen(owner,key,operation,done,S.Datum{D.RowAbsent{}}) == S.Refuse{D.VText{"invalid receipt"}} : S.Action}
def row_absence_during_the_operation_read_is_an_invalid_receipt(owner,key,operation,done): {==}
