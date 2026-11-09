# Actual absolute magnitude fits the full negative signed range, including MIN.
import Base
import ./Value.bend as V
import ./Int64.bend as I
import ./Int64Proofs.bend as A
import ./Int64SignedMagnitude.bend as Signed
import ./Int64RangeBits.bend as Bits
import ./Int64Flags.bend as G
import ../proof/Orders.bend as O
import ./ComparisonProofs.bend as C

def actual_sign_case(sign: Bool, +x: V.Int64, +actual: {I.negative(x) == sign : Bool}) ->
  {I.out_of_range(True{}, I.magnitude(x)) == False{} : Bool}:
  match sign:
    case False{}:
      Equal.trans(Bool, I.out_of_range(True{}, I.magnitude(x)), I.out_of_range(True{}, x), False{},
        Equal.cong(V.Int64, Bool, word => I.out_of_range(True{}, word), I.magnitude(x), x, Signed.magnitude_given_actual_sign(x, False{}, actual)),
        Equal.trans(Bool, I.out_of_range(True{}, x), I.negative(x) && Bool.not(I.negative(Bits.opposite(x))), False{},
          Bits.actual_negative_range_is_exact_opposite_sign_guard(x),
          Equal.cong(Bool, Bool, negative => negative && Bool.not(I.negative(Bits.opposite(x))), I.negative(x), False{}, actual)))
    case True{}:
      Equal.trans(Bool, I.out_of_range(True{}, I.magnitude(x)), I.out_of_range(True{}, Bits.opposite(x)), False{},
        Equal.cong(V.Int64, Bool, word => I.out_of_range(True{}, word), I.magnitude(x), Bits.opposite(x), Signed.magnitude_given_actual_sign(x, True{}, actual)),
        Equal.trans(Bool, I.out_of_range(True{}, Bits.opposite(x)), I.negative(Bits.opposite(x)) && Bool.not(I.negative(Bits.opposite(Bits.opposite(x)))), False{},
          Bits.actual_negative_range_is_exact_opposite_sign_guard(Bits.opposite(x)),
          Equal.trans(Bool, I.negative(Bits.opposite(x)) && Bool.not(I.negative(Bits.opposite(Bits.opposite(x)))), I.negative(Bits.opposite(x)) && Bool.not(True{}), False{},
            Equal.cong(Bool, Bool, sign => I.negative(Bits.opposite(x)) && Bool.not(sign), I.negative(Bits.opposite(Bits.opposite(x))), True{},
              Equal.trans(Bool, I.negative(Bits.opposite(Bits.opposite(x))), I.negative(x), True{},
                Equal.cong(V.Int64, Bool, I.negative, Bits.opposite(Bits.opposite(x)), x, Signed.opposite_is_an_involution(x)), actual)),
            Signed.right_false(I.negative(Bits.opposite(x))))))

law actual_magnitude_is_inside_negative_range:
  for +x: V.Int64
  {I.out_of_range(True{}, I.magnitude(x)) == False{} : Bool}
def actual_magnitude_is_inside_negative_range(x):
  actual_sign_case(I.negative(x), x, {==})

law reverse_not_lt_entails_le:
  for +order: Cmp
  for not_greater: {Cmp.is_lt(order) == False{} : Bool}
  {Cmp.is_le(C.reverse_cmp(order)) == True{} : Bool}
def reverse_not_lt_entails_le(order, not_greater):
  match order:
    case LT{}: Equal.sym(Bool, True{}, False{}, not_greater)
    case EQ{}: {==}
    case GT{}: {==}

law actual_magnitude_word_is_at_most_sign_threshold:
  for +x: V.Int64
  {Cmp.is_le(Word.cmp(64n, A.bits(I.magnitude(x)), A.sign_threshold(63n))) == True{} : Bool}
def actual_magnitude_word_is_at_most_sign_threshold(x):
  not_greater = Equal.trans(Bool, Cmp.is_lt(Word.cmp(64n, A.sign_threshold(63n), A.bits(I.magnitude(x)))),
    I.out_of_range(True{}, I.magnitude(x)), False{},
    Equal.sym(Bool, I.out_of_range(True{}, I.magnitude(x)), Cmp.is_lt(Word.cmp(64n, A.sign_threshold(63n), A.bits(I.magnitude(x)))),
      G.unsigned_lt_is_word_order(V.Int64{2147483648, 0}, I.magnitude(x))), actual_magnitude_is_inside_negative_range(x))
  %Equal.sym(Cmp, Word.cmp(64n, A.bits(I.magnitude(x)), A.sign_threshold(63n)),
    C.reverse_cmp(Word.cmp(64n, A.sign_threshold(63n), A.bits(I.magnitude(x)))),
    Bits.reversed_word_comparison(64n, A.sign_threshold(63n), A.bits(I.magnitude(x)))) :
    {Cmp.is_le(_) == True{} : Bool}
  reverse_not_lt_entails_le(Word.cmp(64n, A.sign_threshold(63n), A.bits(I.magnitude(x))), not_greater)
