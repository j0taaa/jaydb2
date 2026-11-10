# Deliberately false complete lifetime claim; must reject at its proof body.
import Base
import ../../../../contract/Data.bend as D
import ../VoucherPairProofs.bend as P
import ../../Voucher.bend as V
import ../VoucherLifetimeRetire.bend as Retire

def rows() -> List<&2,D.Row>: P.rows("alice","q","tea",False{},Nil{})

law false_reject_voucher_pair_retirement_keeps_its_own_business:
  {D.find_row(Retire.rows("q",rows()),V.voucher("q")) == Some{P.voucher_row("alice","q","tea")} : Maybe<&2,D.Row>}
def false_reject_voucher_pair_retirement_keeps_its_own_business(): {==}
