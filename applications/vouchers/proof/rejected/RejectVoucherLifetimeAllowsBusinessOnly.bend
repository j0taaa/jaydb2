# Deliberately false complete lifetime claim; must reject at its proof body.
import Base
import ../VoucherLifetimeMeaning.bend as I
import ../VoucherPairProofs.bend as P



law false_reject_voucher_lifetime_allows_business_only:
  I.At("alice","q",None{},Some{P.voucher_row("alice","q","tea")})
def false_reject_voucher_lifetime_allows_business_only(): Unit{}
