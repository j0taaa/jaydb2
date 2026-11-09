import Base
import ../../../library/Value.bend as V
import ../../../library/Int64DivisionProofs.bend as P
import ../../../library/Int64DivisionSpec.bend as S

law false_negative_signed_always_none:
  S.DivisionCorrect(V.Int64{0,0},V.Int64{0,1},None{})
def false_negative_signed_always_none():
  P.checked_divmod_is_truncating_integer_division(V.Int64{0,0},V.Int64{0,1})
