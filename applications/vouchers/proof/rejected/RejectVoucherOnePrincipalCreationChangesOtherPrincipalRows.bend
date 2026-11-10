# Deliberately false complete lifetime claim; must reject at its proof body.
import Base
import ../../../../contract/Data.bend as D
import ../VoucherLifetimeState.bend as State
import ../VoucherPairProofs.bend as P
import ../../Initial.bend as Initial

def created() -> D.State: State.transformed_state(State.PairCreated{"q","tea"},"alice",D.State{Initial.tables(),Nil{}},[Initial.gate("alice")])

law false_reject_voucher_one_principal_creation_changes_other_principal_rows:
  {D.rows_collection(D.Application{"bob"},created()) == Some{P.rows("alice","q","tea",False{},[Initial.gate("alice")])} : Maybe<&2,List<&2,D.Row>>}
def false_reject_voucher_one_principal_creation_changes_other_principal_rows(): {==}
