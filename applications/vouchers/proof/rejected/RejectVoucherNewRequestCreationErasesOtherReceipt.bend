# Deliberately false complete lifetime claim; must reject at its proof body.
import Base
import ../../../../contract/Data.bend as D
import ../VoucherPairProofs.bend as P
import ../../Voucher.bend as V

def rows() -> List<&2,D.Row>: P.rows("alice","q","tea",False{},Nil{})

law false_reject_voucher_new_request_creation_erases_other_receipt:
  {D.find_row(P.rows("alice","new","coffee",False{},rows()),V.receipt("q")) == None{} : Maybe<&2,D.Row>}
def false_reject_voucher_new_request_creation_erases_other_receipt(): {==}
