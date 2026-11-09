import Base
import ../../../library/Value.bend as V
import ../../../library/Int64.bend as I
import ../../../library/Int64UnsignedDivision.bend as D
import ../../../contract/Logic.bend as L

law false_negative_unsigned_quotient:
  D.Euclidean(V.Int64{0,6},V.Int64{0,2},I.Division{V.Int64{0,4},V.Int64{0,0}})
def false_negative_unsigned_quotient():
  L.Both{{==},L.Both{{==},{==}}}
