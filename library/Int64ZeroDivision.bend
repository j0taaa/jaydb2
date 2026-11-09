# Zero division has no Euclidean meaning; the actual rejection is justified.
import Base
import ./Value.bend as V
import ./Int64.bend as I
import ../proof/Foundations.bend as F
import ./Int64DivisionSpec.bend as S

def exclude_zero_divisor(+a: V.Int64, +b: V.Int64, zero: {I.zero(b) == True{} : Bool},
  +q: V.Int64, +r: V.Int64, meaning: S.Meaning<a, b, q, r>) -> Empty:
  match meaning:
    case S.Meaning{nonzero, equation, small, quotient_sign, remainder_sign, integer_equation}:
      F.false_negative_true(Equal.trans(Bool, False{}, I.zero(b), True{}, Equal.sym(Bool, I.zero(b), False{}, nonzero), zero))

law zero_divisor_rejection_has_no_mathematical_candidate:
  for +a: V.Int64
  for +b: V.Int64
  for zero: {I.zero(b) == True{} : Bool}
  S.DivisionCorrect(a, b, None{})
def zero_divisor_rejection_has_no_mathematical_candidate(a, b, zero):
  +q => +r => meaning => exclude_zero_divisor(a, b, zero, q, r, meaning)
