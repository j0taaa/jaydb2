# Deliberately false complete lifetime claim; must reject at its proof body.
import Base
import ../../../../contract/Data.bend as D
import ../VoucherPairProofs.bend as P
import ../../Voucher.bend as V
import ../VoucherLifetimePermission.bend as Gate

def rows() -> List<&2,D.Row>: P.rows("alice","q","tea",False{},Nil{})

law false_reject_voucher_gate_update_erases_existing_pair:
  {D.find_row(D.insert_row(rows(),Gate.row("alice",False{})),V.receipt("q")) == None{} : Maybe<&2,D.Row>}
def false_reject_voucher_gate_update_erases_existing_pair(): {==}
