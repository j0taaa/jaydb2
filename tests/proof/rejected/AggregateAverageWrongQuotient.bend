import Base
import ../../../library/Value.bend as V
import ../../../library/Aggregate.bend as Aggregate
import ../../../library/Summary.bend as Summary

law false:
  {Aggregate.average([V.Int64{0,1},V.Int64{0,2}]) == Some{V.Int64{0,2}} : Maybe<&2,V.Int64>}
def false(): {==}
