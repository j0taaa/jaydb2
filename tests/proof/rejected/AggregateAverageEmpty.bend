import Base
import ../../../library/Value.bend as V
import ../../../library/Aggregate.bend as Aggregate
import ../../../library/Summary.bend as Summary

law false:
  {Aggregate.average([]) == Some{V.Int64{0,0}} : Maybe<&2,V.Int64>}
def false(): {==}
