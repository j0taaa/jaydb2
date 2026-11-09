# Returning Some is insufficient: the value must denote the exact integer sum.
import Base
import ../../../library/Value.bend as V
import ../../../library/Int64Proofs.bend as P

law false_zero_plus_zero_is_one:
  P.AdditionCorrect(V.Int64{0, 0}, V.Int64{0, 0}, Some{V.Int64{0, 1}})
def false_zero_plus_zero_is_one():
  P.checked_add_is_integer_addition(V.Int64{0, 0}, V.Int64{0, 0})
