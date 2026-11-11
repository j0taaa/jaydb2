import Base
import ../../../library/Value.bend as V
import ../../../library/Int64.bend as I
import ../../../library/Aggregate.bend as Aggregate

law false:
  {I.lt(V.Int64{2147483648,0},V.Int64{0,0}) == False{} : Bool}
def false(): {==}
