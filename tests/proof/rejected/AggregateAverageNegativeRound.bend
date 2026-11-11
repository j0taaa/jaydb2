import Base
import ../../../library/Value.bend as V
import ../../../library/Aggregate.bend as Aggregate
import ../../../library/Summary.bend as Summary

law false:
  {Aggregate.average([V.Int64{4294967295,4294967295},V.Int64{4294967295,4294967294}]) == Some{V.Int64{4294967295,4294967294}} : Maybe<&2,V.Int64>}
def false(): {==}
