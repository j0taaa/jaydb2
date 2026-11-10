# Actual pair deletion ends precisely one ID lifetime and preserves every
# other complete pair. No canonicality assumption or completed outcome premise.
import Base
import ./VoucherLifetimeMeaning.bend as I
import ./VoucherLifetimeCreate.bend as Keys
import ../../../library/RowRemovalLookupProofs.bend as Remove
import ../Voucher.bend as V
import ./VoucherKeyProofs.bend as K
import ../../../contract/Data.bend as D
import ../../../library/CollectionFrameProofs.bend as Frame
import ../../../proof/Orders.bend as O

def rows(+request: String,old: List<&2,D.Row>) -> List<&2,D.Row>:
  D.remove_row(D.remove_row(old,V.receipt(request)),V.voucher(request))

law actual_pair_deletion_excludes_its_own_receipt_key:
  for +request: String
  for +old: List<&2,D.Row>
  {D.find_row(rows(request,old),V.receipt(request)) == None{} : Maybe<&2,D.Row>}
def actual_pair_deletion_excludes_its_own_receipt_key(request,old):
  Equal.trans(Maybe<&2,D.Row>,D.find_row(rows(request,old),V.receipt(request)),D.find_row(D.remove_row(old,V.receipt(request)),V.receipt(request)),None{},Remove.actual_row_removal_preserves_every_other_exact_key_lookup(D.remove_row(old,V.receipt(request)),V.voucher(request),V.receipt(request),Frame.different_strings_have_symmetric_inequality(V.receipt(request),V.voucher(request),K.actual_receipt_and_voucher_key_spaces_are_disjoint(request,request))),Remove.actual_row_removal_excludes_every_occurrence_of_its_own_key(old,V.receipt(request)))

law actual_pair_deletion_excludes_its_own_voucher_key:
  for +request: String
  for +old: List<&2,D.Row>
  {D.find_row(rows(request,old),V.voucher(request)) == None{} : Maybe<&2,D.Row>}
def actual_pair_deletion_excludes_its_own_voucher_key(request,old):
  Remove.actual_row_removal_excludes_every_occurrence_of_its_own_key(D.remove_row(old,V.receipt(request)),V.voucher(request))

law pair_deletion_preserves_every_other_request_receipt_lookup:
  for +written: String
  for +query: String
  for +old: List<&2,D.Row>
  for different: {String.eq(query,written) == False{} : Bool}
  {D.find_row(rows(written,old),V.receipt(query)) == D.find_row(old,V.receipt(query)) : Maybe<&2,D.Row>}
def pair_deletion_preserves_every_other_request_receipt_lookup(written,query,old,different):
  Equal.trans(Maybe<&2,D.Row>,D.find_row(rows(written,old),V.receipt(query)),D.find_row(D.remove_row(old,V.receipt(written)),V.receipt(query)),D.find_row(old,V.receipt(query)),Remove.actual_row_removal_preserves_every_other_exact_key_lookup(D.remove_row(old,V.receipt(written)),V.voucher(written),V.receipt(query),Frame.different_strings_have_symmetric_inequality(V.receipt(query),V.voucher(written),K.actual_receipt_and_voucher_key_spaces_are_disjoint(query,written))),Remove.actual_row_removal_preserves_every_other_exact_key_lookup(old,V.receipt(written),V.receipt(query),Keys.receipt_keys_of_distinct_requests_are_different(written,query,different)))

law pair_deletion_preserves_every_other_request_voucher_lookup:
  for +written: String
  for +query: String
  for +old: List<&2,D.Row>
  for different: {String.eq(query,written) == False{} : Bool}
  {D.find_row(rows(written,old),V.voucher(query)) == D.find_row(old,V.voucher(query)) : Maybe<&2,D.Row>}
def pair_deletion_preserves_every_other_request_voucher_lookup(written,query,old,different):
  Equal.trans(Maybe<&2,D.Row>,D.find_row(rows(written,old),V.voucher(query)),D.find_row(D.remove_row(old,V.receipt(written)),V.voucher(query)),D.find_row(old,V.voucher(query)),Remove.actual_row_removal_preserves_every_other_exact_key_lookup(D.remove_row(old,V.receipt(written)),V.voucher(written),V.voucher(query),Keys.voucher_keys_of_distinct_requests_are_different(written,query,different)),Remove.actual_row_removal_preserves_every_other_exact_key_lookup(old,V.receipt(written),V.voucher(query),K.actual_receipt_and_voucher_key_spaces_are_disjoint(written,query)))

def removed_request(+owner: String,+written: String,+old: List<&2,D.Row>) -> I.Request(owner,written,rows(written,old)):
  %Equal.sym(Maybe<&2,D.Row>,D.find_row(rows(written,old),V.receipt(written)),None{},actual_pair_deletion_excludes_its_own_receipt_key(written,old)) : I.At(owner,written,_,D.find_row(rows(written,old),V.voucher(written)))
  %Equal.sym(Maybe<&2,D.Row>,D.find_row(rows(written,old),V.voucher(written)),None{},actual_pair_deletion_excludes_its_own_voucher_key(written,old)) : I.At(owner,written,None{},_)
  Unit{}
def request_case(same: Bool,+owner: String,+written: String,+old: List<&2,D.Row>,+query: String,+actual: {String.eq(query,written) == same : Bool},previous: I.Lifetime(owner,old)) -> I.Request(owner,query,rows(written,old)):
  match same:
    case True{}:
      %Equal.sym(String,query,written,O.string_equal(query,written,actual)) : I.Request(owner,_,rows(written,old))
      removed_request(owner,written,old)
    case False{}: I.same_views(owner,query,old,rows(written,old),pair_deletion_preserves_every_other_request_receipt_lookup(written,query,old,actual),pair_deletion_preserves_every_other_request_voucher_lookup(written,query,old,actual),previous(query))

law actual_pair_deletion_preserves_the_complete_bidirectional_all_request_lifetime_invariant:
  for +owner: String
  for +written: String
  for +old: List<&2,D.Row>
  for previous: I.Lifetime(owner,old)
  I.Lifetime(owner,rows(written,old))
def actual_pair_deletion_preserves_the_complete_bidirectional_all_request_lifetime_invariant(owner,written,old,previous):
  query => request_case(String.eq(query,written),owner,written,old,query,{==},previous)
