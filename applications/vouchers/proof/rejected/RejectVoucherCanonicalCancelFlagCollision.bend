# Deliberately false actual voucher behavior; must reject at the proof body.
import Base
import ../../Voucher.bend as V



law false_reject_voucher_canonical_cancel_flag_collision:
  {String.eq(V.canonical("tea",False{}),V.canonical("tea",True{})) == True{} : Bool}
def false_reject_voucher_canonical_cancel_flag_collision(): {==}
