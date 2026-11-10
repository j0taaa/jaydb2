# Deliberately false actual voucher behavior; must reject at the proof body.
import Base
import ../../../../contract/Semantics.bend as S
import ../../Voucher.bend as V



law false_reject_voucher_dispatch_skips_present_permission_check:
  {V.dispatch("alice",V.Issue{"q","tea",False{}}) == V.command("alice",V.Issue{"q","tea",False{}}) : S.Action}
def false_reject_voucher_dispatch_skips_present_permission_check(): {==}
