# A total arithmetic specification cannot accept an always-None implementation.
import Base
import ../../../library/Value.bend as V
import ../../../library/Int64Proofs.bend as P

law false:
  P.AdditionCorrect(V.Int64{0, 0}, V.Int64{0, 0}, None{})
def false():
  P.checked_add_is_integer_addition(V.Int64{0, 0}, V.Int64{0, 0})
