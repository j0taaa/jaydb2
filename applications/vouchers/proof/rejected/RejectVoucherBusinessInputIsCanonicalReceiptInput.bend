# Deliberately false actual voucher behavior; must reject at the proof body.
import Base
import ../../../../contract/Data.bend as D
import ../../Voucher.bend as V



law false_reject_voucher_business_input_is_canonical_receipt_input:
  {D.find_field(V.fields("alice",V.voucher("q"),"tea",V.operation(),V.voucher("q")),"input") == Some{D.VText{V.canonical("tea",False{})}} : Maybe<&2,D.Value>}
def false_reject_voucher_business_input_is_canonical_receipt_input(): {==}
