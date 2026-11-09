import Base
import ../../../library/Value.bend as V
import ../../../library/Int64.bend as I
import ../../../library/Int64DivisionProofs.bend as P

law false_negative_signed_zero_divisor:
  {I.divmod(V.Int64{0,1},V.Int64{0,0}) == Some{I.Division{V.Int64{0,0},V.Int64{0,0}}} : Maybe<&2,I.Division>}
def false_negative_signed_zero_divisor(): {==}
