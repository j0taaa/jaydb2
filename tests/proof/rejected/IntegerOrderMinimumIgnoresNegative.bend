import Base
import ../../../library/Value.bend as V
import ../../../library/Int64.bend as I
import ../../../library/Aggregate.bend as Aggregate

law false_negative_minimum_can_ignore_negative_values:
  {Aggregate.min_value([V.Int64{2147483648,0},V.Int64{2147483647,4294967295},V.Int64{0,0}]) == Some{V.Int64{0,0}} : Maybe<&2,V.Int64>}
def false_negative_minimum_can_ignore_negative_values(): {==}
