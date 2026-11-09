import Base
import ../../../library/Value.bend as V
import ../../../library/Int64.bend as I
import ../../../library/Int64DivisionProofs.bend as P

law false_negative_signed_quotient_sign:
  {I.divmod(V.Int64{0,7},V.Int64{4294967295,4294967293}) == Some{I.Division{V.Int64{0,2},V.Int64{0,1}}} : Maybe<&2,I.Division>}
def false_negative_signed_quotient_sign(): {==}
