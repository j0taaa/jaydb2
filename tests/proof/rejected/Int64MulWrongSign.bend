import Base
import ../../../library/Value.bend as V
import ../../../library/Int64.bend as I
import ../../../library/Int64Multiplication.bend as P

law false:
  {I.mul(V.Int64{4294967295,4294967294},V.Int64{0,3}) == Some{V.Int64{0,6}} : Maybe<&2,V.Int64>}
def false(): {==}
