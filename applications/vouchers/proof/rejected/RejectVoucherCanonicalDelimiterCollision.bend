# Deliberately false actual voucher behavior; must reject at the proof body.
import Base
import ../../Voucher.bend as V



law false_reject_voucher_canonical_delimiter_collision:
  {String.eq(V.canonical("1:tea",False{}),V.canonical("0:tea",True{})) == True{} : Bool}
def false_reject_voucher_canonical_delimiter_collision(): {==}
