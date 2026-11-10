# Deliberately false complete lifetime claim; must reject at its proof body.
import Base
import ../../../../contract/Data.bend as D
import ../VoucherLifetimeMeaning.bend as I
import ../VoucherPairProofs.bend as P
import ../../Voucher.bend as V

def rows() -> List<&2,D.Row>: P.rows("alice","q","tea",False{},Nil{})

law false_reject_voucher_business_only_deletion_preserves_pair:
  I.Request("alice","q",D.remove_row(rows(),V.voucher("q")))
def false_reject_voucher_business_only_deletion_preserves_pair(): Unit{}
