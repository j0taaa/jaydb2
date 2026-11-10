# Deliberately false complete lifetime claim; must reject at its proof body.
import Base
import ../../../../contract/Data.bend as D
import ../VoucherLifetimeMeaning.bend as I
import ../VoucherPairProofs.bend as P
import ../../Voucher.bend as V
import ../../../../library/ValueScalarProofs.bend as Pair



law false_reject_voucher_lifetime_allows_invented_result:
  I.At("alice","q",Some{D.Row{V.receipt("q"),V.fields("alice",V.receipt("q"),V.canonical("tea",False{}),V.operation(),"invented-result")}},Some{P.voucher_row("alice","q","tea")})
def false_reject_voucher_lifetime_allows_invented_result(): ("tea",Pair.Both{{==},{==}})
