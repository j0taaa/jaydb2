# Deliberately false complete lifetime claim; must reject at its proof body.
import Base
import ../VoucherLifetimeMeaning.bend as I
import ../VoucherPairProofs.bend as P
import ../../../../library/ValueScalarProofs.bend as Pair



law false_reject_voucher_lifetime_ignores_principal_binding:
  I.At("bob","q",Some{P.receipt_row("alice","q","tea",False{})},Some{P.voucher_row("alice","q","tea")})
def false_reject_voucher_lifetime_ignores_principal_binding(): ("tea",Pair.Both{{==},{==}})
