import Base
import ../../../library/Value.bend as V
import ../../../library/Int64.bend as I
import ../../../library/Int64UnsignedDivision.bend as D

law false:
  {I.divide_step(64n,V.Int64{0,7},V.Int64{0,3},V.Int64{0,0},V.Int64{0,0}) == I.Division{V.Int64{0,0},V.Int64{0,7}} : I.Division}
def false(): {==}
