# A total arithmetic specification cannot accept an always-None implementation.
import Base
import ../../../library/Value.bend as V
import ../../../library/Int64Proofs.bend as P

law false_zero_plus_zero_may_be_rejected:
  P.AdditionCorrect(V.Int64{0, 0}, V.Int64{0, 0}, None{})
def false_zero_plus_zero_may_be_rejected():
  P.checked_add_is_integer_addition(V.Int64{0, 0}, V.Int64{0, 0})
