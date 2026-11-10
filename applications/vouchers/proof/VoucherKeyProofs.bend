# Actual frozen Voucher runtime, staged by EXACT import-only substitutions.
# Source binding hashes + identical non-import bytes are checked separately.
# Encodings are injective over ALL String DATA, with no Unicode normalization.
import Base
import ../Voucher.bend as V
import ../../../contract/Logic.bend as L
import ../../../proof/Foundations.bend as F

def tail(s: String) -> String:
  match s:
    case SNil{}: SNil{}
    case SCon{head,rest}: rest

law a_common_literal_string_prefix_cancels_from_exact_concatenation:
  for +prefix: String
  for +left: String
  for +right: String
  for same: {String.append(prefix,left) == String.append(prefix,right) : String}
  {left == right : String}
def a_common_literal_string_prefix_cancels_from_exact_concatenation(prefix,left,right,same):
  match prefix:
    case SNil{}: same
    case SCon{head,+rest}: a_common_literal_string_prefix_cancels_from_exact_concatenation(rest,left,right,Equal.cong(String,String,tail,String.append(SCon{head,rest},left),String.append(SCon{head,rest},right),same))

law actual_receipt_request_keys_are_injective:
  for +left: String
  for +right: String
  for same: {V.receipt(left) == V.receipt(right) : String}
  {left == right : String}
def actual_receipt_request_keys_are_injective(left,right,same): a_common_literal_string_prefix_cancels_from_exact_concatenation("r:",left,right,same)

law actual_voucher_request_keys_are_injective:
  for +left: String
  for +right: String
  for same: {V.voucher(left) == V.voucher(right) : String}
  {left == right : String}
def actual_voucher_request_keys_are_injective(left,right,same): a_common_literal_string_prefix_cancels_from_exact_concatenation("v:",left,right,same)

law actual_receipt_and_voucher_key_spaces_are_disjoint:
  for +receipt_request: String
  for +voucher_request: String
  {String.eq(V.receipt(receipt_request),V.voucher(voucher_request)) == False{} : Bool}
def actual_receipt_and_voucher_key_spaces_are_disjoint(receipt_request,voucher_request): {==}

law actual_receipt_keys_cannot_replace_the_permission_gate:
  for +request: String
  {String.eq(V.receipt(request),"permission") == False{} : Bool}
def actual_receipt_keys_cannot_replace_the_permission_gate(request): {==}

law actual_voucher_keys_cannot_replace_the_permission_gate:
  for +request: String
  {String.eq(V.voucher(request),"permission") == False{} : Bool}
def actual_voucher_keys_cannot_replace_the_permission_gate(request): {==}

def starts_zero(s: String) -> Bool:
  match s:
    case SNil{}: False{}
    case SCon{Chr{code},rest}: U32.is_eq(code,48)

def contrary_prefixes(+left: String,+right: String,same: {left == right : String},zero: {starts_zero(left) == True{} : Bool},one: {starts_zero(right) == False{} : Bool}) -> Empty:
  F.false_negative_true(Equal.trans(Bool,False{},starts_zero(right),True{},Equal.sym(Bool,starts_zero(right),False{},one),Equal.trans(Bool,starts_zero(right),starts_zero(left),True{},Equal.sym(Bool,starts_zero(left),starts_zero(right),Equal.cong(String,Bool,starts_zero,left,right,same)),zero)))

law actual_canonical_input_is_injective_in_both_text_and_cancellation_flag:
  for +left: String
  for +left_cancel: Bool
  for +right: String
  for +right_cancel: Bool
  for same: {V.canonical(left,left_cancel) == V.canonical(right,right_cancel) : String}
  L.E<{left == right : String},{left_cancel == right_cancel : Bool}>
def actual_canonical_input_is_injective_in_both_text_and_cancellation_flag(left,left_cancel,right,right_cancel,same):
  match left_cancel right_cancel:
    case False{} False{}: L.Both{a_common_literal_string_prefix_cancels_from_exact_concatenation("0:",left,right,same),{==}}
    case True{} True{}: L.Both{a_common_literal_string_prefix_cancels_from_exact_concatenation("1:",left,right,same),{==}}
    case False{} True{}: Empty.absurd(L.E<{left == right : String},{False{} == True{} : Bool}>,contrary_prefixes(V.canonical(left,False{}),V.canonical(right,True{}),same,{==},{==}))
    case True{} False{}: Empty.absurd(L.E<{left == right : String},{True{} == False{} : Bool}>,contrary_prefixes(V.canonical(right,False{}),V.canonical(left,True{}),Equal.sym(String,V.canonical(left,True{}),V.canonical(right,False{}),same),{==},{==}))
