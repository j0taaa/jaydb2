import Base
import ../../../library/Value.bend as V
import ../../../library/Int64.bend as I
import ../../../library/Int64DivisionProofs.bend as P

# -7=3*(-3)+2 is an ordinary integer equation but is floor division,
# rather than the promised quotient truncation toward zero.
law false_negative_signed_floor_rounding:
  {I.divmod(V.Int64{4294967295,4294967289},V.Int64{0,3}) == Some{I.Division{V.Int64{4294967295,4294967293},V.Int64{0,2}}} : Maybe<&2,I.Division>}
def false_negative_signed_floor_rounding(): {==}
