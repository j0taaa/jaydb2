# Actual permission-gate row cannot collide with either side of ANY request
# pair; updating it therefore preserves the complete lifetime relation.
import Base
import ./VoucherLifetimeMeaning.bend as I
import ../Voucher.bend as V
import ../Initial.bend as Initial
import ./VoucherKeyProofs.bend as K
import ../../../library/RowLookupProofs.bend as Row
import ../../../contract/Data.bend as D
import ../../../library/CollectionFrameProofs.bend as Frame

def row(owner: String,enabled: Bool) -> D.Row:
  D.Row{"permission",[D.Field{"enabled",D.VBool{enabled}},D.Field{"id",D.VText{"permission"}},D.Field{"input",D.VAbsent{}},D.Field{"operation",D.VAbsent{}},D.Field{"owner",D.VText{owner}},D.Field{"result",D.VAbsent{}}]}

law actual_permission_row_upsert_preserves_the_complete_lifetime_invariant:
  for +owner: String
  for +enabled: Bool
  for +old: List<&2,D.Row>
  for previous: I.Lifetime(owner,old)
  I.Lifetime(owner,D.insert_row(old,row(owner,enabled)))
def actual_permission_row_upsert_preserves_the_complete_lifetime_invariant(owner,enabled,old,previous):
  query => I.same_views(owner,query,old,D.insert_row(old,row(owner,enabled)),Row.an_actual_upsert_preserves_every_other_exact_key_lookup(old,row(owner,enabled),V.receipt(query),Frame.different_strings_have_symmetric_inequality(V.receipt(query),"permission",K.actual_receipt_keys_cannot_replace_the_permission_gate(query))),Row.an_actual_upsert_preserves_every_other_exact_key_lookup(old,row(owner,enabled),V.voucher(query),Frame.different_strings_have_symmetric_inequality(V.voucher(query),"permission",K.actual_voucher_keys_cannot_replace_the_permission_gate(query))),previous(query))

law an_empty_table_has_no_live_unpaired_request:
  for +owner: String
  I.Lifetime(owner,Nil{})
def an_empty_table_has_no_live_unpaired_request(owner): query => Unit{}

law the_actual_frozen_initial_gate_table_has_the_complete_lifetime_invariant:
  for +owner: String
  I.Lifetime(owner,[Initial.gate(owner)])
def the_actual_frozen_initial_gate_table_has_the_complete_lifetime_invariant(owner):
  actual_permission_row_upsert_preserves_the_complete_lifetime_invariant(owner,True{},Nil{},an_empty_table_has_no_live_unpaired_request(owner))
