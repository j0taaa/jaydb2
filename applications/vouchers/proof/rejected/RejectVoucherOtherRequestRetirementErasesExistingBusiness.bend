# Deliberately false complete lifetime claim; must reject at its proof body.
import Base
import ../../../../contract/Data.bend as D
import ../VoucherPairProofs.bend as P
import ../../Voucher.bend as V
import ../VoucherLifetimeRetire.bend as Retire

def rows() -> List<&2,D.Row>: P.rows("alice","q","tea",False{},Nil{})

law false_reject_voucher_other_request_retirement_erases_existing_business:
  {D.find_row(Retire.rows("new",rows()),V.voucher("q")) == None{} : Maybe<&2,D.Row>}
def false_reject_voucher_other_request_retirement_erases_existing_business(): {==}
