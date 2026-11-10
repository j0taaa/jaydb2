# Deliberately false complete lifetime claim; must reject at its proof body.
import Base
import ../VoucherLifetimeMeaning.bend as I
import ../VoucherPairProofs.bend as P



law false_reject_voucher_lifetime_allows_receipt_only:
  I.At("alice","q",Some{P.receipt_row("alice","q","tea",False{})},None{})
def false_reject_voucher_lifetime_allows_receipt_only(): Unit{}
