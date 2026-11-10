# Deliberately false actual voucher behavior; must reject at the proof body.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Logic.bend as L
import ../VoucherPairProofs.bend as P

def state(rows: List<&2,D.Row>) -> D.State: D.State{[D.Table{"alice",rows}],Nil{}}

law false_reject_voucher_receipt_alone_proves_business_correspondence:
  P.PairState("alice","q","tea",False{},state([P.receipt_row("alice","q","tea",False{})]))
def false_reject_voucher_receipt_alone_proves_business_correspondence(): L.Both{{==},{==}}
