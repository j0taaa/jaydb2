import Base
import ../../../library/Value.bend as V
import ../../../library/Int64Multiplication.bend as M

# Even zero times one has a required successful signed result.
law false_signed_always_none:
  M.MultiplicationCorrect(V.Int64{0,0},V.Int64{0,1},None{})
def false_signed_always_none():
  M.checked_mul_is_integer_multiplication(V.Int64{0,0},V.Int64{0,1})
