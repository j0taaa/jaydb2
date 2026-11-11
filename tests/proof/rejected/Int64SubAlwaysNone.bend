# The total mathematical subtraction contract cannot accept always-None.
import Base
import ../../../library/Int64Subtraction.bend as P
import ../../../library/Value.bend as V

law false:
  P.SubtractionCorrect(V.Int64{0, 0}, V.Int64{0, 0}, None{})
def false():
  P.checked_sub_is_integer_subtraction(V.Int64{0, 0}, V.Int64{0, 0})
