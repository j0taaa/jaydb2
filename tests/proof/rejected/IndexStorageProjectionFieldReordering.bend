# Deliberately false functional claim; must reject at its proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../library/Index.bend as I
import ../../../library/Query.bend as Q

law false_reject_projection_field_reordering:
  {I.projection(Q.Selected{D.VRecord{"value",D.VText{"v"},D.VRecord{"target",D.VText{"t"},D.VRecordEmpty{}}}}) == I.Target{"t","v"} : I.Projection}
def false_reject_projection_field_reordering(): {==}
