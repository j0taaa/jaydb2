# Complete checked signed multiplication against ordinary integer arithmetic.
# The independent integer product is (ap*bp+an*bn) - (ap*bn+an*bp),
# with each input interpreted as its unsigned bit value minus its sign radix.
import Base
import ./Int64IntegerProduct.bend as P
import ./Int64ProductInterpretation.bend as Product
import ./Int64UnsignedMultiply.bend as U
import ./Int64SignedMagnitude.bend as Signed
import ./Value.bend as V
import ./Int64.bend as I
import ./Int64Proofs.bend as A

def MultiplicationCorrect(+a: V.Int64,+b: V.Int64,result: Maybe<&2,V.Int64>) -> Type:
  match result:
    case Some{r}: Product.IntegerProduct(a,b,r)
    case None{}: @r: V.Int64 -> Product.IntegerProduct(a,b,r) -> Empty

# A checked conversion preserves exact products and rejects only when every
# signed-word candidate for the mathematical product is impossible.
def conversion_result_is_product(+a: V.Int64,+b: V.Int64,+x: V.Int64,result: Maybe<&2,V.Int64>,
  measured: {A.unsigned(x) == Product.magnitude_product(a,b) : Nat},
  correct: Signed.SignedResult(Product.sign(a,b),x,result)) -> MultiplicationCorrect(a,b,result):
  match result:
    case Some{+r}:
      Product.signed_magnitude_product_is_integer_product(a,b,r,
        (%measured : P.IntegerEqual(A.integer(r),P.sign_integer(Product.sign(a,b),_))
          correct))
    case None{}:
      +r => exact => correct(r,
        (%Equal.sym(Nat,A.unsigned(x),Product.magnitude_product(a,b),measured) : P.IntegerEqual(A.integer(r),P.sign_integer(Product.sign(a,b),_))
          Product.integer_product_is_signed_magnitude_product(a,b,r,exact)))

# Case analysis follows the actual unsigned result, never an assumed output.
def unsigned_result_is_product(+a: V.Int64,+b: V.Int64,result: Maybe<&2,V.Int64>,
  correct: U.UnsignedResult(Product.magnitude_product(a,b),result)) ->
  MultiplicationCorrect(a,b,I.sign_result(Product.sign(a,b),result)):
  match result:
    case Some{+x}:
      conversion_result_is_product(a,b,x,I.signed(Product.sign(a,b),x),correct,Signed.actual_signed_is_integer_magnitude(Product.sign(a,b),x))
    case None{}:
      +r => exact => correct(I.magnitude(r),Product.candidate_magnitude(r,Product.sign(a,b),Product.magnitude_product(a,b),Product.integer_product_is_signed_magnitude_product(a,b,r,exact)))

# No output, carry, overflow, sign, loop invariant or fuel fact is a premise.
# None refutes every signed 64-bit candidate for the independent integer result.
law checked_mul_is_integer_multiplication:
  for +a: V.Int64
  for +b: V.Int64
  MultiplicationCorrect(a,b,I.mul(a,b))
def checked_mul_is_integer_multiplication(a,b):
  unsigned_result_is_product(a,b,I.multiply_step(64n,I.magnitude(a),I.magnitude(b),V.Int64{0,0}),U.unsigned_multiply_is_natural_product(I.magnitude(a),I.magnitude(b)))
