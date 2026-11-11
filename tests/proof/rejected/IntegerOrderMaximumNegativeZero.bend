import Base
import ../../../library/Value.bend as V
import ../../../library/Int64.bend as I
import ../../../library/Aggregate.bend as Aggregate

law false:
  {Aggregate.max_value([V.Int64{4294967295,4294967294},V.Int64{4294967295,4294967295}]) == Some{V.Int64{0,0}} : Maybe<&2,V.Int64>}
def false(): {==}
