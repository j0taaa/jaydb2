# Deliberately false functional claim; must reject at its proof body.
import Base
import ../../../contract/Data.bend as D
import ../../../library/Index.bend as I
import ../../../library/Query.bend as Q

law false:
  {I.projection(Q.Selected{D.VRecord{"target",D.VInt{0,1},D.VRecord{"value",D.VText{"v"},D.VRecordEmpty{}}}}) == I.Target{"1","v"} : I.Projection}
def false(): {==}
