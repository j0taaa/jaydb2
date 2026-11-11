import Base
import ../../../library/Value.bend as V
import ../../../library/Int64.bend as I
import ../../../library/Aggregate.bend as Aggregate

law false:
  {Aggregate.minimum([V.Int64{0,5}],V.Int64{4294967295,4294967289}) == V.Int64{0,5} : V.Int64}
def false(): {==}
