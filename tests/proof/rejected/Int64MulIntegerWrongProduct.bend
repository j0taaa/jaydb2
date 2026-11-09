import Base
import ../../../library/Value.bend as V
import ../../../library/Int64Multiplication.bend as M

law false_integer_product:
  M.MultiplicationCorrect(V.Int64{0,2},V.Int64{0,3},Some{V.Int64{0,7}})
def false_integer_product(): {==}
