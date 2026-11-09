# The arithmetic product specification is independent of the signed-magnitude
# implementation. Its link uses the proved interpretation of actual magnitudes.
import Base
import ./Int64IntegerProduct.bend as P
import ./Int64Magnitude.bend as M
import ./Int64Proofs.bend as A
import ./Int64.bend as I
import ./Value.bend as V

# Separately elaborated specifications are connected explicitly, avoiding an
# appeal to matching names or to equality of opaque neutral eliminators.
law magnitude_equal_bridge:
  for +a: A.Integer
  for +b: A.Integer
  for same: M.IntegerEqual(a,b)
  P.IntegerEqual(a,b)
def magnitude_equal_bridge(a,b,same):
  match a b:
    case A.Integer{ap,an} A.Integer{bp,bn}: same

law magnitude_sign_bridge:
  for +sign: Bool
  for +value: Nat
  {M.sign_integer(sign,value) == P.sign_integer(sign,value) : A.Integer}
def magnitude_sign_bridge(sign,value):
  match sign:
    case False{}: {==}
    case True{}: {==}

law actual_magnitude_for_product:
  for +x: V.Int64
  P.IntegerEqual(A.integer(x),P.sign_integer(I.negative(x),A.unsigned(I.magnitude(x))))
def actual_magnitude_for_product(x):
  %magnitude_sign_bridge(I.negative(x),A.unsigned(I.magnitude(x))) : P.IntegerEqual(A.integer(x),_)
  magnitude_equal_bridge(A.integer(x),M.sign_integer(I.negative(x),A.unsigned(I.magnitude(x))),M.actual_magnitude_is_unsigned_absolute_value(x))

def magnitude_product(+a: V.Int64,+b: V.Int64) -> Nat:
  Nat.mul(A.unsigned(I.magnitude(b)),A.unsigned(I.magnitude(a)))

def sign(+a: V.Int64,+b: V.Int64) -> Bool:
  Bool.xor(I.negative(a),I.negative(b))

def IntegerProduct(+a: V.Int64,+b: V.Int64,r: V.Int64) -> Type:
  P.IntegerEqual(A.integer(r),P.product(A.integer(a),A.integer(b)))

law mathematical_product_has_actual_magnitude_product:
  for +a: V.Int64
  for +b: V.Int64
  P.IntegerEqual(P.product(A.integer(a),A.integer(b)),P.sign_integer(sign(a,b),magnitude_product(a,b)))
def mathematical_product_has_actual_magnitude_product(a,b):
  P.integer_equal_transitive(P.product(A.integer(a),A.integer(b)),P.product(P.sign_integer(I.negative(a),A.unsigned(I.magnitude(a))),P.sign_integer(I.negative(b),A.unsigned(I.magnitude(b)))),P.sign_integer(sign(a,b),magnitude_product(a,b)),
    P.product_respects_equalities(A.integer(a),A.integer(b),P.sign_integer(I.negative(a),A.unsigned(I.magnitude(a))),P.sign_integer(I.negative(b),A.unsigned(I.magnitude(b))),actual_magnitude_for_product(a),actual_magnitude_for_product(b)),
    (%Equal.sym(A.Integer,P.product(P.sign_integer(I.negative(a),A.unsigned(I.magnitude(a))),P.sign_integer(I.negative(b),A.unsigned(I.magnitude(b)))),P.sign_integer(sign(a,b),magnitude_product(a,b)),P.product_of_signed_magnitudes_reversed(I.negative(a),I.negative(b),A.unsigned(I.magnitude(a)),A.unsigned(I.magnitude(b)))) :
      P.IntegerEqual(_,P.sign_integer(sign(a,b),magnitude_product(a,b)))
     P.integer_equal_reflexive(P.sign_integer(sign(a,b),magnitude_product(a,b)))))

law signed_magnitude_product_is_integer_product:
  for +a: V.Int64
  for +b: V.Int64
  for +r: V.Int64
  for exact: P.IntegerEqual(A.integer(r),P.sign_integer(sign(a,b),magnitude_product(a,b)))
  IntegerProduct(a,b,r)
def signed_magnitude_product_is_integer_product(a,b,r,exact):
  P.integer_equal_transitive(A.integer(r),P.sign_integer(sign(a,b),magnitude_product(a,b)),P.product(A.integer(a),A.integer(b)),exact,
    P.integer_equal_symmetric(P.product(A.integer(a),A.integer(b)),P.sign_integer(sign(a,b),magnitude_product(a,b)),mathematical_product_has_actual_magnitude_product(a,b)))

law integer_product_is_signed_magnitude_product:
  for +a: V.Int64
  for +b: V.Int64
  for +r: V.Int64
  for exact: IntegerProduct(a,b,r)
  P.IntegerEqual(A.integer(r),P.sign_integer(sign(a,b),magnitude_product(a,b)))
def integer_product_is_signed_magnitude_product(a,b,r,exact):
  P.integer_equal_transitive(A.integer(r),P.product(A.integer(a),A.integer(b)),P.sign_integer(sign(a,b),magnitude_product(a,b)),exact,mathematical_product_has_actual_magnitude_product(a,b))

# Any candidate for a signed mathematical value has that absolute magnitude.
# This remains valid for zero, with either sign convention.
law candidate_magnitude:
  for +r: V.Int64
  for +negative: Bool
  for +value: Nat
  for exact: P.IntegerEqual(A.integer(r),P.sign_integer(negative,value))
  {A.unsigned(I.magnitude(r)) == value : Nat}
def candidate_magnitude(r,negative,value,exact):
  P.equal_signed_integers_have_equal_magnitudes(I.negative(r),negative,A.unsigned(I.magnitude(r)),value,
    P.integer_equal_transitive(P.sign_integer(I.negative(r),A.unsigned(I.magnitude(r))),A.integer(r),P.sign_integer(negative,value),
      P.integer_equal_symmetric(A.integer(r),P.sign_integer(I.negative(r),A.unsigned(I.magnitude(r))),actual_magnitude_for_product(r)),exact))
