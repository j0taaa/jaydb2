import Base
import ../../../library/Value.bend as V
import ../../../library/Int64.bend as I
import ../../../library/Aggregate.bend as Aggregate

law false:
  {Aggregate.max_value([V.Int64{2147483648,0},V.Int64{2147483647,4294967295},V.Int64{0,0}]) == Some{V.Int64{0,0}} : Maybe<&2,V.Int64>}
def false(): {==}
