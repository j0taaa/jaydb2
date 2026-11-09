import Base
import ../../../library/Value.bend as V
import ../../../library/Int64.bend as I
import ../../../library/Int64UnsignedMultiply.bend as M

law false_lost_shift_carry:
  {I.multiply_step(64n,V.Int64{2147483648,0},V.Int64{0,2},V.Int64{0,0}) == Some{V.Int64{0,0}} : Maybe<&2,V.Int64>}
def false_lost_shift_carry(): {==}
