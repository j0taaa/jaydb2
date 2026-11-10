import Base
import ../../../library/Value.bend as V
import ../../../library/Int64.bend as I
import ../../../library/Aggregate.bend as Aggregate

law false_negative_maximum_has_an_empty_default:
  {Aggregate.max_value([]) == Some{V.Int64{0,0}} : Maybe<&2,V.Int64>}
def false_negative_maximum_has_an_empty_default(): {==}
