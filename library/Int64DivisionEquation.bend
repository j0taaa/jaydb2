# The unsigned quotient/remainder equation and signed conversions imply a=b*q+r
# in independent ordinary integer arithmetic, without wrapping arithmetic.
import Base
import ./Value.bend as V
import ./Int64.bend as I
import ./Int64Proofs.bend as A
import ./Int64IntegerProduct.bend as P
import ./Int64ProductInterpretation.bend as Product
import ./Int64IntegerAddition.bend as Add

law quotient_sign_cancels_divisor_sign:
  for a: Bool
  for b: Bool
  {Bool.xor(b, Bool.xor(a, b)) == a : Bool}
def quotient_sign_cancels_divisor_sign(a, b):
  match a b:
    case False{} False{}: {==}
    case False{} True{}: {==}
    case True{} False{}: {==}
    case True{} True{}: {==}

law divisor_times_quotient_has_dividend_sign:
  for +a: V.Int64
  for +b: V.Int64
  for +q: V.Int64
  for +uq: V.Int64
  for quotient: P.IntegerEqual(A.integer(q), P.sign_integer(Bool.xor(I.negative(a), I.negative(b)), A.unsigned(uq)))
  P.IntegerEqual(P.product(A.integer(b), A.integer(q)), P.sign_integer(I.negative(a), Nat.mul(A.unsigned(I.magnitude(b)), A.unsigned(uq))))
def divisor_times_quotient_has_dividend_sign(a, b, q, uq, quotient):
  +signed_product = Equal.trans(A.Integer,
    P.product(P.sign_integer(I.negative(b), A.unsigned(I.magnitude(b))), P.sign_integer(Bool.xor(I.negative(a), I.negative(b)), A.unsigned(uq))),
    P.sign_integer(Bool.xor(I.negative(b), Bool.xor(I.negative(a), I.negative(b))), Nat.mul(A.unsigned(I.magnitude(b)), A.unsigned(uq))),
    P.sign_integer(I.negative(a), Nat.mul(A.unsigned(I.magnitude(b)), A.unsigned(uq))),
    P.product_of_signed_magnitudes(I.negative(b), Bool.xor(I.negative(a), I.negative(b)), A.unsigned(I.magnitude(b)), A.unsigned(uq)),
    Equal.cong(Bool, A.Integer, sign => P.sign_integer(sign, Nat.mul(A.unsigned(I.magnitude(b)), A.unsigned(uq))),
      Bool.xor(I.negative(b), Bool.xor(I.negative(a), I.negative(b))), I.negative(a), quotient_sign_cancels_divisor_sign(I.negative(a), I.negative(b))))
  %signed_product : P.IntegerEqual(P.product(A.integer(b), A.integer(q)), _)
  P.product_respects_equalities(A.integer(b), A.integer(q), P.sign_integer(I.negative(b), A.unsigned(I.magnitude(b))),
    P.sign_integer(Bool.xor(I.negative(a), I.negative(b)), A.unsigned(uq)), Product.actual_magnitude_for_product(b), quotient)

law signed_quotient_and_remainder_satisfy_the_integer_equation:
  for +a: V.Int64
  for +b: V.Int64
  for +q: V.Int64
  for +r: V.Int64
  for +uq: V.Int64
  for +ur: V.Int64
  for equation: {A.unsigned(I.magnitude(a)) == Nat.add(Nat.mul(A.unsigned(I.magnitude(b)), A.unsigned(uq)), A.unsigned(ur)) : Nat}
  for quotient: P.IntegerEqual(A.integer(q), P.sign_integer(Bool.xor(I.negative(a), I.negative(b)), A.unsigned(uq)))
  for remainder: P.IntegerEqual(A.integer(r), P.sign_integer(I.negative(a), A.unsigned(ur)))
  A.IntegerSum(P.product(A.integer(b), A.integer(q)), A.integer(r), A.integer(a))
def signed_quotient_and_remainder_satisfy_the_integer_equation(a, b, q, r, uq, ur, equation, quotient, remainder):
  +sum_layout = Equal.trans(A.Integer,
    Add.add(P.sign_integer(I.negative(a), Nat.mul(A.unsigned(I.magnitude(b)), A.unsigned(uq))), P.sign_integer(I.negative(a), A.unsigned(ur))),
    P.sign_integer(I.negative(a), Nat.add(Nat.mul(A.unsigned(I.magnitude(b)), A.unsigned(uq)), A.unsigned(ur))),
    P.sign_integer(I.negative(a), A.unsigned(I.magnitude(a))),
    Add.same_sign_adds_magnitudes(I.negative(a), Nat.mul(A.unsigned(I.magnitude(b)), A.unsigned(uq)), A.unsigned(ur)),
    Equal.cong(Nat, A.Integer, magnitude => P.sign_integer(I.negative(a), magnitude),
      Nat.add(Nat.mul(A.unsigned(I.magnitude(b)), A.unsigned(uq)), A.unsigned(ur)), A.unsigned(I.magnitude(a)),
      Equal.sym(Nat, A.unsigned(I.magnitude(a)), Nat.add(Nat.mul(A.unsigned(I.magnitude(b)), A.unsigned(uq)), A.unsigned(ur)), equation)))
  P.integer_equal_transitive(Add.add(P.product(A.integer(b), A.integer(q)), A.integer(r)),
    P.sign_integer(I.negative(a), A.unsigned(I.magnitude(a))), A.integer(a),
    (%sum_layout : P.IntegerEqual(Add.add(P.product(A.integer(b), A.integer(q)), A.integer(r)), _)
      Add.addition_respects_integer_equalities(P.product(A.integer(b), A.integer(q)), A.integer(r),
        P.sign_integer(I.negative(a), Nat.mul(A.unsigned(I.magnitude(b)), A.unsigned(uq))), P.sign_integer(I.negative(a), A.unsigned(ur)),
        divisor_times_quotient_has_dividend_sign(a, b, q, uq, quotient), remainder)),
    P.integer_equal_symmetric(A.integer(a), P.sign_integer(I.negative(a), A.unsigned(I.magnitude(a))), Product.actual_magnitude_for_product(a)))
