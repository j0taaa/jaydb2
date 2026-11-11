import Base
import ../../../library/Value.bend as V
import ../../../library/Int64.bend as I
import ../../../library/Aggregate.bend as Aggregate

law false:
  {I.lt(V.Int64{4294967295,4294967294},V.Int64{4294967295,4294967295}) == False{} : Bool}
def false(): {==}
