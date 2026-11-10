# Deliberately false actual voucher behavior; must reject at the proof body.
import Base
import ../../Voucher.bend as V



law false_reject_voucher_receipt_and_business_prefix_collision:
  {String.eq(V.receipt("v:q"),V.voucher("r:q")) == True{} : Bool}
def false_reject_voucher_receipt_and_business_prefix_collision(): {==}
