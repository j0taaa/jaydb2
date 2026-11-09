# Complete actual checked unsigned-magnitude-to-signed conversion.
import Base
import ./Value.bend as V
import ./Int64.bend as I
import ./Int64Proofs.bend as A
import ./Int64Subtraction.bend as Sub
import ../proof/Foundations.bend as F
import ../proof/CodecAcceptanceTags.bend as Tags
import ./Int64IntegerProduct.bend as P
import ./Int64ProductInterpretation.bend as Product
import ./Int64MagnitudeCore.bend as M
import ./Int64RangeBits.bend as Bits

law unsigned_value_is_injective:
  for +a: V.Int64
  for +b: V.Int64
  for same: {A.unsigned(a) == A.unsigned(b) : Nat}
  {a == b : V.Int64}
def unsigned_value_is_injective(a, b, same):
  A.bits_injective(a, b, Tags.word_to_nat_injective(64n, A.bits(a), A.bits(b), same))

law wrapping_add_commutes:
  for +a: V.Int64
  for +b: V.Int64
  {I.wrapping_add(a, b) == I.wrapping_add(b, a) : V.Int64}
def wrapping_add_commutes(a, b):
  A.bits_injective(I.wrapping_add(a, b), I.wrapping_add(b, a),
    Equal.trans(Word(64n), A.bits(I.wrapping_add(a, b)), Word.add(64n, A.bits(a), A.bits(b)), A.bits(I.wrapping_add(b, a)),
      A.wrapping_add_is_full_word_add(a, b),
      Equal.trans(Word(64n), Word.add(64n, A.bits(a), A.bits(b)), Word.add(64n, A.bits(b), A.bits(a)), A.bits(I.wrapping_add(b, a)),
        Word.add_comm(64n, A.bits(a), A.bits(b)),
        Equal.sym(Word(64n), A.bits(I.wrapping_add(b, a)), Word.add(64n, A.bits(b), A.bits(a)), A.wrapping_add_is_full_word_add(b, a)))))

law opposite_is_an_involution:
  for +x: V.Int64
  {Bits.opposite(Bits.opposite(x)) == x : V.Int64}
def opposite_is_an_involution(x):
  +sum = Equal.trans(V.Int64, I.wrapping_add(Bits.opposite(x), x), I.wrapping_add(x, Bits.opposite(x)), V.Int64{0, 0},
    wrapping_add_commutes(Bits.opposite(x), x), Sub.wrapping_add_undoes_subtraction(V.Int64{0, 0}, x))
  Equal.trans(V.Int64, Bits.opposite(Bits.opposite(x)), I.wrapping_sub(I.wrapping_add(Bits.opposite(x), x), Bits.opposite(x)), x,
    Equal.cong(V.Int64, V.Int64, value => I.wrapping_sub(value, Bits.opposite(x)), V.Int64{0, 0}, I.wrapping_add(Bits.opposite(x), x),
      Equal.sym(V.Int64, I.wrapping_add(Bits.opposite(x), x), V.Int64{0, 0}, sum)),
    Sub.wrapping_subtraction_undoes_add(Bits.opposite(x), x))

law magnitude_given_actual_sign:
  for +x: V.Int64
  for +sign: Bool
  for actual: {I.negative(x) == sign : Bool}
  {I.magnitude(x) == Bool.pick(V.Int64, sign, Bits.opposite(x), x) : V.Int64}
def magnitude_given_actual_sign(x, sign, actual):
  Equal.cong(Bool, V.Int64, negative => Bool.pick(V.Int64, negative, Bits.opposite(x), x), I.negative(x), sign, actual)

law sum_zero_right:
  for a: Nat
  for +b: Nat
  for same: {Nat.add(a, b) == 0n : Nat}
  {b == 0n : Nat}
def sum_zero_right(a, b, same):
  match a:
    case 0n: same
    case 1n+p:
      F.absurd_boolean({b == 0n : Nat}, Equal.cong(Nat, Bool, A.nat_zero, 1n+Nat.add(p, b), 0n, same))

law right_false:
  for b: Bool
  {b && False{} == False{} : Bool}
def right_false(b):
  match b:
    case False{}: {==}
    case True{}: {==}

law not_false_is_true:
  for b: Bool
  for no: {Bool.not(b) == False{} : Bool}
  {b == True{} : Bool}
def not_false_is_true(b, no):
  match b:
    case False{}: F.absurd_boolean({False{} == True{} : Bool}, Equal.sym(Bool, True{}, False{}, no))
    case True{}: {==}

law opposite_sign_is_negative_when_range_fits:
  for +x: V.Int64
  for negative: {I.negative(x) == True{} : Bool}
  for fits: {I.out_of_range(True{}, x) == False{} : Bool}
  {I.negative(Bits.opposite(x)) == True{} : Bool}
def opposite_sign_is_negative_when_range_fits(x, negative, fits):
  true = Equal.trans(Bool, True{} && Bool.not(I.negative(Bits.opposite(x))), I.negative(x) && Bool.not(I.negative(Bits.opposite(x))), False{},
    Equal.cong(Bool, Bool, b => b && Bool.not(I.negative(Bits.opposite(x))), True{}, I.negative(x), Equal.sym(Bool, I.negative(x), True{}, negative)),
    Equal.trans(Bool, I.negative(x) && Bool.not(I.negative(Bits.opposite(x))), I.out_of_range(True{}, x), False{},
      Equal.sym(Bool, I.out_of_range(True{}, x), I.negative(x) && Bool.not(I.negative(Bits.opposite(x))), Bits.actual_negative_range_is_exact_opposite_sign_guard(x)), fits))
  not_false_is_true(I.negative(Bits.opposite(x)), true)

# Full primitive families are not involved here: all copied evidence is Data equality.
def zero_from_mismatched_signs(sa: Bool, sb: Bool, +a: Nat, +b: Nat,
  different: {Bool.xor(sa, sb) == True{} : Bool}, same: P.IntegerEqual(P.sign_integer(sa, a), P.sign_integer(sb, b))) -> {b == 0n : Nat}:
  match sa sb:
    case False{} False{}: F.absurd_boolean({b == 0n : Nat}, different)
    case True{} True{}: F.absurd_boolean({b == 0n : Nat}, different)
    case False{} True{}: sum_zero_right(a, b, same)
    case True{} False{}:
      sum_zero_right(a, b, Equal.sym(Nat, 0n, Nat.add(a, b),
        Equal.trans(Nat, 0n, Nat.add(b, a), Nat.add(a, b), same, A.add_commutative(b, a))))

def signed_equation(+r: V.Int64, +negative: Bool, +value: Nat,
  exact: P.IntegerEqual(A.integer(r), P.sign_integer(negative, value))) ->
  P.IntegerEqual(P.sign_integer(I.negative(r), A.unsigned(I.magnitude(r))), P.sign_integer(negative, value)):
  P.integer_equal_transitive(P.sign_integer(I.negative(r), A.unsigned(I.magnitude(r))), A.integer(r), P.sign_integer(negative, value),
    P.integer_equal_symmetric(A.integer(r), P.sign_integer(I.negative(r), A.unsigned(I.magnitude(r))), Product.actual_magnitude_for_product(r)), exact)

law zero_magnitude_target_always_fits:
  for +negative: Bool
  for +x: V.Int64
  for zero: {A.unsigned(x) == 0n : Nat}
  {I.out_of_range(negative, x) == False{} : Bool}
def zero_magnitude_target_always_fits(negative, x, zero):
  match negative:
    case False{}:
      Equal.cong(V.Int64, Bool, value => I.out_of_range(False{}, value), x, V.Int64{0, 0}, unsigned_value_is_injective(x, V.Int64{0, 0}, zero))
    case True{}:
      Equal.cong(V.Int64, Bool, value => I.out_of_range(True{}, value), x, V.Int64{0, 0}, unsigned_value_is_injective(x, V.Int64{0, 0}, zero))

# Every mathematical signed candidate forces the actual range guard to accept.
def candidate_with_known_sign(negative: Bool, sign: Bool, +x: V.Int64, +r: V.Int64,
  +actual_sign: {I.negative(r) == sign : Bool},
  exact: P.IntegerEqual(A.integer(r), P.sign_integer(negative, A.unsigned(x)))) -> {I.out_of_range(negative, x) == False{} : Bool}:
  match negative sign:
    case False{} False{}:
      +magnitude = unsigned_value_is_injective(I.magnitude(r), x, Product.candidate_magnitude(r, False{}, A.unsigned(x), exact))
      +same = Equal.trans(V.Int64, r, I.magnitude(r), x,
        Equal.sym(V.Int64, I.magnitude(r), r, magnitude_given_actual_sign(r, False{}, actual_sign)), magnitude)
      Equal.trans(Bool, I.negative(x), I.negative(r), False{},
        Equal.cong(V.Int64, Bool, I.negative, x, r, Equal.sym(V.Int64, r, x, same)), actual_sign)
    case True{} True{}:
      +same = Equal.trans(V.Int64, Bits.opposite(r), I.magnitude(r), x,
        Equal.sym(V.Int64, I.magnitude(r), Bits.opposite(r), magnitude_given_actual_sign(r, True{}, actual_sign)),
        unsigned_value_is_injective(I.magnitude(r), x, Product.candidate_magnitude(r, True{}, A.unsigned(x), exact)))
      +opposite = Equal.trans(V.Int64, Bits.opposite(x), Bits.opposite(Bits.opposite(r)), r,
        Equal.cong(V.Int64, V.Int64, Bits.opposite, x, Bits.opposite(r), Equal.sym(V.Int64, Bits.opposite(r), x, same)), opposite_is_an_involution(r))
      Equal.trans(Bool, I.out_of_range(True{}, x), I.negative(x) && Bool.not(I.negative(Bits.opposite(x))), False{},
        Bits.actual_negative_range_is_exact_opposite_sign_guard(x),
        Equal.trans(Bool, I.negative(x) && Bool.not(I.negative(Bits.opposite(x))), I.negative(x) && Bool.not(True{}), False{},
          Equal.cong(Bool, Bool, sign => I.negative(x) && Bool.not(sign), I.negative(Bits.opposite(x)), True{},
            Equal.trans(Bool, I.negative(Bits.opposite(x)), I.negative(r), True{}, Equal.cong(V.Int64, Bool, I.negative, Bits.opposite(x), r, opposite), actual_sign)),
          right_false(I.negative(x))))
    case True{} False{}:
      same = signed_equation(r, True{}, A.unsigned(x), exact)
      zero_magnitude_target_always_fits(True{}, x,
        zero_from_mismatched_signs(False{}, True{}, A.unsigned(I.magnitude(r)), A.unsigned(x), {==},
          (%actual_sign : P.IntegerEqual(P.sign_integer(_, A.unsigned(I.magnitude(r))), P.sign_integer(True{}, A.unsigned(x)))
            same)))
    case False{} True{}:
      same = signed_equation(r, False{}, A.unsigned(x), exact)
      zero_magnitude_target_always_fits(False{}, x,
        zero_from_mismatched_signs(True{}, False{}, A.unsigned(I.magnitude(r)), A.unsigned(x), {==},
          (%actual_sign : P.IntegerEqual(P.sign_integer(_, A.unsigned(I.magnitude(r))), P.sign_integer(False{}, A.unsigned(x)))
            same)))

law representable_signed_magnitude_forces_fitting:
  for +negative: Bool
  for +x: V.Int64
  for +r: V.Int64
  for exact: P.IntegerEqual(A.integer(r), P.sign_integer(negative, A.unsigned(x)))
  {I.out_of_range(negative, x) == False{} : Bool}
def representable_signed_magnitude_forces_fitting(negative, x, r, exact):
  candidate_with_known_sign(negative, I.negative(r), x, r, {==}, exact)

law nonnegative_word_is_its_unsigned_integer:
  for +x: V.Int64
  for nonnegative: {I.negative(x) == False{} : Bool}
  P.IntegerEqual(A.integer(x), P.sign_integer(False{}, A.unsigned(x)))
def nonnegative_word_is_its_unsigned_integer(x, nonnegative):
  %Equal.sym(A.Integer, A.integer(x), A.Integer{A.unsigned(x), A.spill(64n, I.negative(x))}, M.integer_uses_actual_sign(x)) :
    P.IntegerEqual(_, P.sign_integer(False{}, A.unsigned(x)))
  %Equal.sym(Bool, I.negative(x), False{}, nonnegative) :
    P.IntegerEqual(A.Integer{A.unsigned(x), A.spill(64n, _)}, P.sign_integer(False{}, A.unsigned(x)))
  {==}

def unsigned_zero_difference_equation(+x: V.Int64,
  known: {A.integer(x) == A.Integer{A.unsigned(x), 0n} : A.Integer},
  exact: Sub.IntegerDifference(A.integer(V.Int64{0, 0}), A.integer(x), A.integer(Bits.opposite(x)))) ->
  A.IntegerSum(A.Integer{A.unsigned(x), 0n}, A.integer(Bits.opposite(x)), A.integer(V.Int64{0, 0})):
  %known : A.IntegerSum(_, A.integer(Bits.opposite(x)), A.integer(V.Int64{0, 0}))
  exact

def zero_difference_is_negative_unsigned(+x: V.Int64,
  known: {A.integer(x) == A.Integer{A.unsigned(x), 0n} : A.Integer},
  exact: Sub.IntegerDifference(A.integer(V.Int64{0, 0}), A.integer(x), A.integer(Bits.opposite(x)))) ->
  P.IntegerEqual(A.integer(Bits.opposite(x)), P.sign_integer(True{}, A.unsigned(x))):
  sum = unsigned_zero_difference_equation(x, known, exact)
  Equal.trans(Nat, Nat.add(A.unsigned(Bits.opposite(x)), A.unsigned(x)), Nat.add(A.unsigned(x), A.unsigned(Bits.opposite(x))),
    A.spill(64n, A.top(64n, A.bits(Bits.opposite(x)))), A.add_commutative(A.unsigned(Bits.opposite(x)), A.unsigned(x)),
    Equal.trans(Nat, Nat.add(A.unsigned(x), A.unsigned(Bits.opposite(x))), Nat.add(Nat.add(A.unsigned(x), A.unsigned(Bits.opposite(x))), 0n),
      A.spill(64n, A.top(64n, A.bits(Bits.opposite(x)))),
      Equal.sym(Nat, Nat.add(Nat.add(A.unsigned(x), A.unsigned(Bits.opposite(x))), 0n), Nat.add(A.unsigned(x), A.unsigned(Bits.opposite(x))),
        A.add_zero_right(Nat.add(A.unsigned(x), A.unsigned(Bits.opposite(x))))), sum))

law negating_nonnegative_unsigned_has_exact_negative_value:
  for +x: V.Int64
  for +nonnegative: {I.negative(x) == False{} : Bool}
  P.IntegerEqual(A.integer(Bits.opposite(x)), P.sign_integer(True{}, A.unsigned(x)))
def negating_nonnegative_unsigned_has_exact_negative_value(x, nonnegative):
  +known = Equal.trans(A.Integer, A.integer(x), A.Integer{A.unsigned(x), A.spill(64n, I.negative(x))}, A.Integer{A.unsigned(x), 0n},
    M.integer_uses_actual_sign(x),
    Equal.cong(Bool, A.Integer, sign => A.Integer{A.unsigned(x), A.spill(64n, sign)}, I.negative(x), False{}, nonnegative))
  fits = Equal.cong(Bool, Bool, sign => Bool.xor(False{}, sign) && Bool.xor(False{}, I.negative(Bits.opposite(x))), I.negative(x), False{}, nonnegative)
  zero_difference_is_negative_unsigned(x, known, Sub.fitting_subtraction_is_integer_difference(V.Int64{0, 0}, x, fits))

law fitting_negative_unsigned_has_exact_negative_value:
  for +x: V.Int64
  for negative: {I.negative(x) == True{} : Bool}
  for fits: {I.out_of_range(True{}, x) == False{} : Bool}
  P.IntegerEqual(A.integer(Bits.opposite(x)), P.sign_integer(True{}, A.unsigned(x)))
def fitting_negative_unsigned_has_exact_negative_value(x, negative, fits):
  +opposite_negative = opposite_sign_is_negative_when_range_fits(x, negative, fits)
  +magnitude = Equal.trans(V.Int64, I.magnitude(Bits.opposite(x)), Bits.opposite(Bits.opposite(x)), x,
    magnitude_given_actual_sign(Bits.opposite(x), True{}, opposite_negative), opposite_is_an_involution(x))
  +right = Equal.trans(A.Integer, P.sign_integer(I.negative(Bits.opposite(x)), A.unsigned(I.magnitude(Bits.opposite(x)))),
    P.sign_integer(True{}, A.unsigned(I.magnitude(Bits.opposite(x)))), P.sign_integer(True{}, A.unsigned(x)),
    Equal.cong(Bool, A.Integer, sign => P.sign_integer(sign, A.unsigned(I.magnitude(Bits.opposite(x)))), I.negative(Bits.opposite(x)), True{}, opposite_negative),
    Equal.cong(V.Int64, A.Integer, word => P.sign_integer(True{}, A.unsigned(word)), I.magnitude(Bits.opposite(x)), x, magnitude))
  %right : P.IntegerEqual(A.integer(Bits.opposite(x)), _)
  Product.actual_magnitude_for_product(Bits.opposite(x))

def negative_success_case(sign: Bool, +x: V.Int64, actual: {I.negative(x) == sign : Bool},
  fits: {I.out_of_range(True{}, x) == False{} : Bool}) ->
  P.IntegerEqual(A.integer(Bits.opposite(x)), P.sign_integer(True{}, A.unsigned(x))):
  match sign:
    case False{}: negating_nonnegative_unsigned_has_exact_negative_value(x, actual)
    case True{}: fitting_negative_unsigned_has_exact_negative_value(x, actual, fits)

law fitting_signed_word_is_exact_integer_magnitude:
  for +negative: Bool
  for +x: V.Int64
  for fits: {I.out_of_range(negative, x) == False{} : Bool}
  P.IntegerEqual(A.integer(I.signed_word(negative, x)), P.sign_integer(negative, A.unsigned(x)))
def fitting_signed_word_is_exact_integer_magnitude(negative, x, fits):
  match negative:
    case False{}: nonnegative_word_is_its_unsigned_integer(x, fits)
    case True{}: negative_success_case(I.negative(x), x, {==}, fits)

def SignedResult(+negative: Bool, +x: V.Int64, result: Maybe<&2, V.Int64>) -> Type:
  match result:
    case Some{r}: P.IntegerEqual(A.integer(r), P.sign_integer(negative, A.unsigned(x)))
    case None{}: @r: V.Int64 -> P.IntegerEqual(A.integer(r), P.sign_integer(negative, A.unsigned(x))) -> Empty

def signed_case(over: Bool, +negative: Bool, +x: V.Int64,
  actual: {I.out_of_range(negative, x) == over : Bool}) -> SignedResult(negative, x, I.checked(over, I.signed_word(negative, x))):
  match over:
    case False{}: fitting_signed_word_is_exact_integer_magnitude(negative, x, actual)
    case True{}:
      r => exact => F.false_negative_true(Equal.trans(Bool, False{}, I.out_of_range(negative, x), True{},
        Equal.sym(Bool, I.out_of_range(negative, x), False{}, representable_signed_magnitude_forces_fitting(negative, x, r, exact)), actual))

law actual_signed_is_integer_magnitude:
  for +negative: Bool
  for +x: V.Int64
  SignedResult(negative, x, I.signed(negative, x))
def actual_signed_is_integer_magnitude(negative, x):
  signed_case(I.out_of_range(negative, x), negative, x, {==})
