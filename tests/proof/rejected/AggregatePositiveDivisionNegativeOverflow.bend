import Base
import ../../../library/Value.bend as V
import ../../../library/Int64.bend as I
import ../../../library/Int64PositiveDivision.bend as Positive

law false_negative_all_nonzero_divisors_fit_signed_division:
  {I.divmod(V.Int64{2147483648,0},V.Int64{4294967295,4294967295}) == Some{I.Division{V.Int64{2147483648,0},V.Int64{0,0}}} : Maybe<&2,I.Division>}
def false_negative_all_nonzero_divisors_fit_signed_division(): {==}
