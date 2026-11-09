# Every proper unsigned remainder of a signed64 divisor fits both signed signs.
import Base
import ./Value.bend as V
import ./Int64.bend as I
import ./Int64Proofs.bend as A
import ./Int64Flags.bend as G
import ./Int64RangeBits.bend as Bits
import ./Int64MagnitudeCore.bend as M
import ./Int64SignedMagnitude.bend as Signed
import ./Int64IntegerProduct.bend as P
import ../proof/Orders.bend as O
import ../proof/Foundations.bend as F
import ./Int64MagnitudeBound.bend as Bound

def compose_strict_then_nonstrict(ab: Cmp, bc: Cmp, +ac: Cmp,
  first: {Cmp.is_lt(ab) == True{} : Bool}, second: {Cmp.is_le(bc) == True{} : Bool}, coherent: O.Coherent(ab, bc, ac)) ->
  {Cmp.is_lt(ac) == True{} : Bool}:
  match ab bc:
    case LT{} LT{}: Equal.cong(Cmp, Bool, Cmp.is_lt, ac, LT{}, coherent)
    case LT{} EQ{}: Equal.cong(Cmp, Bool, Cmp.is_lt, ac, LT{}, coherent)
    case LT{} GT{}: F.absurd_boolean({Cmp.is_lt(ac) == True{} : Bool}, second)
    case EQ{} _: F.absurd_boolean({Cmp.is_lt(ac) == True{} : Bool}, first)
    case GT{} _: F.absurd_boolean({Cmp.is_lt(ac) == True{} : Bool}, first)

law proper_remainder_word_is_below_sign_threshold:
  for +remainder: V.Int64
  for +divisor: V.Int64
  for proper: {I.unsigned_lt(remainder, I.magnitude(divisor)) == True{} : Bool}
  {Cmp.is_lt(Word.cmp(64n, A.bits(remainder), A.sign_threshold(63n))) == True{} : Bool}
def proper_remainder_word_is_below_sign_threshold(remainder, divisor, proper):
  compose_strict_then_nonstrict(Word.cmp(64n, A.bits(remainder), A.bits(I.magnitude(divisor))),
    Word.cmp(64n, A.bits(I.magnitude(divisor)), A.sign_threshold(63n)), Word.cmp(64n, A.bits(remainder), A.sign_threshold(63n)),
    Equal.trans(Bool, Cmp.is_lt(Word.cmp(64n, A.bits(remainder), A.bits(I.magnitude(divisor)))), I.unsigned_lt(remainder, I.magnitude(divisor)), True{},
      Equal.sym(Bool, I.unsigned_lt(remainder, I.magnitude(divisor)), Cmp.is_lt(Word.cmp(64n, A.bits(remainder), A.bits(I.magnitude(divisor)))),
        G.unsigned_lt_is_word_order(remainder, I.magnitude(divisor))), proper),
    Bound.actual_magnitude_word_is_at_most_sign_threshold(divisor),
    O.word_coherent(64n, A.bits(remainder), A.bits(I.magnitude(divisor)), A.sign_threshold(63n)))

law proper_remainder_is_nonnegative_word:
  for +remainder: V.Int64
  for +divisor: V.Int64
  for proper: {I.unsigned_lt(remainder, I.magnitude(divisor)) == True{} : Bool}
  {I.negative(remainder) == False{} : Bool}
def proper_remainder_is_nonnegative_word(remainder, divisor, proper):
  Equal.trans(Bool, I.negative(remainder), A.top(64n, A.bits(remainder)), False{}, A.negative_is_sign_bit(remainder),
    Equal.trans(Bool, A.top(64n, A.bits(remainder)), Cmp.is_ge(Word.cmp(64n, A.bits(remainder), A.sign_threshold(63n))), False{},
      Equal.sym(Bool, Cmp.is_ge(Word.cmp(64n, A.bits(remainder), A.sign_threshold(63n))), A.top(64n, A.bits(remainder)), A.sign_threshold_is_top(63n, A.bits(remainder))),
      Equal.cong(Cmp, Bool, Cmp.is_ge, Word.cmp(64n, A.bits(remainder), A.sign_threshold(63n)), LT{},
        M.lt_cmp_is_literal(Word.cmp(64n, A.bits(remainder), A.sign_threshold(63n)), proper_remainder_word_is_below_sign_threshold(remainder, divisor, proper)))))

law every_proper_remainder_fits_either_sign:
  for +negative: Bool
  for +remainder: V.Int64
  for +divisor: V.Int64
  for proper: {I.unsigned_lt(remainder, I.magnitude(divisor)) == True{} : Bool}
  {I.out_of_range(negative, remainder) == False{} : Bool}
def every_proper_remainder_fits_either_sign(negative, remainder, divisor, proper):
  match negative:
    case False{}: proper_remainder_is_nonnegative_word(remainder, divisor, proper)
    case True{}:
      Equal.trans(Bool, I.out_of_range(True{}, remainder), I.negative(remainder) && Bool.not(I.negative(Bits.opposite(remainder))), False{},
        Bits.actual_negative_range_is_exact_opposite_sign_guard(remainder),
        Equal.cong(Bool, Bool, sign => sign && Bool.not(I.negative(Bits.opposite(remainder))), I.negative(remainder), False{},
          proper_remainder_is_nonnegative_word(remainder, divisor, proper)))

law actual_remainder_signing_has_exact_integer_value:
  for +negative: Bool
  for +remainder: V.Int64
  for +divisor: V.Int64
  for proper: {I.unsigned_lt(remainder, I.magnitude(divisor)) == True{} : Bool}
  P.IntegerEqual(A.integer(I.signed_word(negative, remainder)), P.sign_integer(negative, A.unsigned(remainder)))
def actual_remainder_signing_has_exact_integer_value(negative, remainder, divisor, proper):
  Signed.fitting_signed_word_is_exact_integer_magnitude(negative, remainder, every_proper_remainder_fits_either_sign(negative, remainder, divisor, proper))
