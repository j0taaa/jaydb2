# Deliberately false complete lifetime claim; must reject at its proof body.
import Base
import ../../../../contract/Data.bend as D
import ../../Initial.bend as Initial



law false_reject_voucher_origin_forces_an_empty_user_registry:
  {D.State{Initial.tables(),[D.Row{"registry",Nil{}}]} == D.State{Initial.tables(),Nil{}} : D.State}
def false_reject_voucher_origin_forces_an_empty_user_registry(): {==}
