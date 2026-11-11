# A returned word must represent subtraction, not absolute difference.
import Base
import ../../../library/Int64Subtraction.bend as P
import ../../../library/Value.bend as V

law false:
  P.SubtractionCorrect(V.Int64{0, 0}, V.Int64{0, 1}, Some{V.Int64{0, 1}})
def false():
  {==}
