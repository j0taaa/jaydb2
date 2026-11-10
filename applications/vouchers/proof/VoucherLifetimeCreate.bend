# Complete all-request invariant preservation by the ACTUAL two row upserts.
# All input row lists are arbitrary. The previous invariant is an AFFINE
# function proof, called once for the observed request; no Type proof is copied.
import Base
import ./VoucherLifetimeMeaning.bend as I
import ../Voucher.bend as V
import ./VoucherPairProofs.bend as P
import ../../../library/RowLookupProofs.bend as Row
import ./VoucherKeyProofs.bend as K
import ../../../library/ReceiptInputProofs.bend as Text
import ../../../contract/Data.bend as D
import ../../../library/CollectionFrameProofs.bend as Frame
import ../../../proof/Foundations.bend as F
import ../../../proof/Orders.bend as O

def different_requests(+query: String,+written: String,different: {String.eq(query,written) == False{} : Bool},same: {written == query : String}) -> Empty:
  F.false_negative_true(Equal.trans(Bool,False{},String.eq(query,written),True{},Equal.sym(Bool,String.eq(query,written),False{},different),Equal.trans(Bool,String.eq(query,written),String.eq(query,query),True{},Equal.cong(String,Bool,value => String.eq(query,value),written,query,same),O.string_eq_refl(query))))

law receipt_keys_of_distinct_requests_are_different:
  for +written: String
  for +query: String
  for different: {String.eq(query,written) == False{} : Bool}
  {String.eq(V.receipt(written),V.receipt(query)) == False{} : Bool}
def receipt_keys_of_distinct_requests_are_different(written,query,different):
  Text.different_literal_texts_have_a_false_string_equality_comparison(V.receipt(written),V.receipt(query),same => different_requests(query,written,different,K.actual_receipt_request_keys_are_injective(written,query,same)))

law voucher_keys_of_distinct_requests_are_different:
  for +written: String
  for +query: String
  for different: {String.eq(query,written) == False{} : Bool}
  {String.eq(V.voucher(written),V.voucher(query)) == False{} : Bool}
def voucher_keys_of_distinct_requests_are_different(written,query,different):
  Text.different_literal_texts_have_a_false_string_equality_comparison(V.voucher(written),V.voucher(query),same => different_requests(query,written,different,K.actual_voucher_request_keys_are_injective(written,query,same)))

law pair_upserts_preserve_every_other_request_receipt_lookup:
  for +owner: String
  for +written: String
  for +input: String
  for +old: List<&2,D.Row>
  for +query: String
  for different: {String.eq(query,written) == False{} : Bool}
  {D.find_row(P.rows(owner,written,input,False{},old),V.receipt(query)) == D.find_row(old,V.receipt(query)) : Maybe<&2,D.Row>}
def pair_upserts_preserve_every_other_request_receipt_lookup(owner,written,input,old,query,different):
  Equal.trans(Maybe<&2,D.Row>,D.find_row(P.rows(owner,written,input,False{},old),V.receipt(query)),D.find_row(D.insert_row(old,P.voucher_row(owner,written,input)),V.receipt(query)),D.find_row(old,V.receipt(query)),Row.an_actual_upsert_preserves_every_other_exact_key_lookup(D.insert_row(old,P.voucher_row(owner,written,input)),P.receipt_row(owner,written,input,False{}),V.receipt(query),receipt_keys_of_distinct_requests_are_different(written,query,different)),Row.an_actual_upsert_preserves_every_other_exact_key_lookup(old,P.voucher_row(owner,written,input),V.receipt(query),Frame.different_strings_have_symmetric_inequality(V.receipt(query),V.voucher(written),K.actual_receipt_and_voucher_key_spaces_are_disjoint(query,written))))

law pair_upserts_preserve_every_other_request_voucher_lookup:
  for +owner: String
  for +written: String
  for +input: String
  for +old: List<&2,D.Row>
  for +query: String
  for different: {String.eq(query,written) == False{} : Bool}
  {D.find_row(P.rows(owner,written,input,False{},old),V.voucher(query)) == D.find_row(old,V.voucher(query)) : Maybe<&2,D.Row>}
def pair_upserts_preserve_every_other_request_voucher_lookup(owner,written,input,old,query,different):
  Equal.trans(Maybe<&2,D.Row>,D.find_row(P.rows(owner,written,input,False{},old),V.voucher(query)),D.find_row(D.insert_row(old,P.voucher_row(owner,written,input)),V.voucher(query)),D.find_row(old,V.voucher(query)),Row.an_actual_upsert_preserves_every_other_exact_key_lookup(D.insert_row(old,P.voucher_row(owner,written,input)),P.receipt_row(owner,written,input,False{}),V.voucher(query),K.actual_receipt_and_voucher_key_spaces_are_disjoint(written,query)),Row.an_actual_upsert_preserves_every_other_exact_key_lookup(old,P.voucher_row(owner,written,input),V.voucher(query),voucher_keys_of_distinct_requests_are_different(written,query,different)))

def request_case(same: Bool,+owner: String,+written: String,+input: String,+old: List<&2,D.Row>,+query: String,+actual: {String.eq(query,written) == same : Bool},previous: I.Lifetime(owner,old)) -> I.Request(owner,query,P.rows(owner,written,input,False{},old)):
  match same:
    case True{}:
      %Equal.sym(String,query,written,O.string_equal(query,written,actual)) : I.Request(owner,_,P.rows(owner,written,input,False{},old))
      I.from_pair(owner,written,input,old,P.the_two_actual_upserts_create_both_exact_corresponding_rows_for_all_input_row_lists(owner,written,input,False{},old))
    case False{}: I.same_views(owner,query,old,P.rows(owner,written,input,False{},old),pair_upserts_preserve_every_other_request_receipt_lookup(owner,written,input,old,query,actual),pair_upserts_preserve_every_other_request_voucher_lookup(owner,written,input,old,query,actual),previous(query))

law actual_pair_upserts_preserve_the_complete_bidirectional_all_request_lifetime_invariant:
  for +owner: String
  for +written: String
  for +input: String
  for +old: List<&2,D.Row>
  for previous: I.Lifetime(owner,old)
  I.Lifetime(owner,P.rows(owner,written,input,False{},old))
def actual_pair_upserts_preserve_the_complete_bidirectional_all_request_lifetime_invariant(owner,written,input,old,previous):
  query => request_case(String.eq(query,written),owner,written,input,old,query,{==},previous)
