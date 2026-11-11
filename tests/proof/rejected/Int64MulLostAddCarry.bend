import Base
import ../../../library/Value.bend as V
import ../../../library/Int64.bend as I
import ../../../library/Int64UnsignedMultiply.bend as M

law false:
  {I.multiply_step(64n,V.Int64{0,1},V.Int64{0,1},V.Int64{4294967295,4294967295}) == Some{V.Int64{0,0}} : Maybe<&2,V.Int64>}
def false(): {==}
