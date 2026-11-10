# Deliberately false actual voucher behavior; must reject at the proof body.
import Base
import ../../../../contract/Data.bend as D
import ../../Voucher.bend as V

def permission(enabled: Bool) -> D.Row: D.Row{"permission",[D.Field{"enabled",D.VBool{enabled}},D.Field{"id",D.VText{"permission"}},D.Field{"input",D.VAbsent{}},D.Field{"operation",D.VAbsent{}},D.Field{"owner",D.VText{"alice"}},D.Field{"result",D.VAbsent{}}]}

law false_reject_voucher_receipt_key_overwrites_permission_gate:
  {String.eq(V.receipt("permission"),"permission") == True{} : Bool}
def false_reject_voucher_receipt_key_overwrites_permission_gate(): {==}
