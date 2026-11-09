# Independent signed Euclidean meaning: truncation toward zero, dividend-sign
# remainder, strict absolute remainder bound, and the ordinary integer equation.
# Absolute values use the separately proved actual magnitude interpretation.
import Base
import ./Value.bend as V
import ./Int64.bend as I
import ./Int64Proofs.bend as A
import ./Int64IntegerProduct.bend as P

def absolute(x: V.Int64) -> Nat:
  A.unsigned(I.magnitude(x))

def quotient_sign(a: V.Int64, b: V.Int64) -> Bool:
  Bool.xor(I.negative(a), I.negative(b))

type Meaning<-a: V.Int64, -b: V.Int64, -q: V.Int64, -r: V.Int64> is Type:
  Meaning{nonzero: {I.zero(b) == False{} : Bool},
    magnitude_equation: {absolute(a) == Nat.add(Nat.mul(absolute(b), absolute(q)), absolute(r)) : Nat},
    small_remainder: {Nat.is_lt(absolute(r), absolute(b)) == True{} : Bool},
    quotient_sign: P.IntegerEqual(A.integer(q), P.sign_integer(quotient_sign(a, b), absolute(q))),
    remainder_sign: P.IntegerEqual(A.integer(r), P.sign_integer(I.negative(a), absolute(r))),
    integer_equation: A.IntegerSum(P.product(A.integer(b), A.integer(q)), A.integer(r), A.integer(a))}

def DivisionCorrect(+a: V.Int64, +b: V.Int64, result: Maybe<&2, I.Division>) -> Type:
  match result:
    case Some{I.Division{q, r}}: Meaning<a, b, q, r>
    case None{}: @q: V.Int64 -> @r: V.Int64 -> Meaning<a, b, q, r> -> Empty
