import Base
import ../../../library/Value.bend as V
import ../../../library/Int64.bend as I
import ../../../library/Int64Multiplication.bend as P

# The positive magnitude 2^63 is rejected rather than wrapped to MIN.
law false_minimum_negation:
  {I.mul(V.Int64{2147483648,0},V.Int64{4294967295,4294967295}) == Some{V.Int64{2147483648,0}} : Maybe<&2,V.Int64>}
def false_minimum_negation(): {==}
