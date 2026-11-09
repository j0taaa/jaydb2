# A nonzero nonnegative signed divisor cannot overflow signed division.
# The unsigned Euclidean equation bounds the quotient by the dividend's
# absolute magnitude, including the representable negative MIN magnitude.
import Base
import ./Value.bend as V
import ./Int64.bend as I
import ./Int64Proofs.bend as A
import ./Int64SignedMagnitude.bend as Signed
import ./Int64ProductInterpretation.bend as Product
import ./Int64RemainderRange.bend as Range
import ./Int64NaturalOrder.bend as Order
import ./Int64UnsignedDivision.bend as Unsigned
import ./Int64MagnitudeBound.bend as Bound
import ./Int64MagnitudeZero.bend as Zero
import ./Int64DivisionSigning.bend as Signing
import ./Int64DivisionSpec.bend as Division
import ../contract/Logic.bend as L
import ../proof/Foundations.bend as F

law addition_is_at_least_its_first_summand:
  for +a: Nat
  for +b: Nat
  {Nat.is_le(a,Nat.add(a,b)) == True{} : Bool}
def addition_is_at_least_its_first_summand(a,b):
  match a b:
    case 0n 0n: {==}
    case 0n 1n+p: {==}
    case 1n+p b: addition_is_at_least_its_first_summand(p,b)

law positive_division_bounds_quotient:
  for +a: Nat
  for +d: Nat
  for +q: Nat
  for +r: Nat
  for positive: {Nat.is_lt(0n,d) == True{} : Bool}
  for equation: {a == Nat.add(Nat.mul(d,q),r) : Nat}
  {Nat.is_le(q,a) == True{} : Bool}
def positive_division_bounds_quotient(a,d,q,r,positive,equation):
  match d:
    case 0n: F.absurd_boolean({Nat.is_le(q,a) == True{} : Bool},positive)
    case 1n+p:
      %Equal.sym(Nat,a,Nat.add(q,Nat.add(Nat.mul(p,q),r)),Equal.trans(Nat,a,Nat.add(Nat.add(q,Nat.mul(p,q)),r),Nat.add(q,Nat.add(Nat.mul(p,q),r)),equation,A.add_associative(q,Nat.mul(p,q),r))) : {Nat.is_le(q,_) == True{} : Bool}
      addition_is_at_least_its_first_summand(q,Nat.add(Nat.mul(p,q),r))

law equal_natural_comparison_is_equality:
  for +a: Nat
  for +b: Nat
  for same: {Nat.cmp(a,b) == EQ{} : Cmp}
  {a == b : Nat}
def equal_natural_comparison_is_equality(a,b,same):
  match a b:
    case 0n 0n: {==}
    case 0n 1n+p: F.absurd_boolean({0n == 1n+p : Nat},Equal.cong(Cmp,Bool,Cmp.is_eq,LT{},EQ{},same))
    case 1n+p 0n: F.absurd_boolean({1n+p == 0n : Nat},Equal.cong(Cmp,Bool,Cmp.is_eq,GT{},EQ{},same))
    case 1n+p 1n+q: Equal.cong(Nat,Nat,n => 1n+n,p,q,equal_natural_comparison_is_equality(p,q,same))

def bounded_quotient_case(order: Cmp,+a: V.Int64,+q: V.Int64,
  actual: {Nat.cmp(A.unsigned(q),Division.absolute(a)) == order : Cmp},less: {Cmp.is_le(order) == True{} : Bool}) ->
  {I.out_of_range(I.negative(a),q) == False{} : Bool}:
  match order:
    case LT{}:
      Range.every_proper_remainder_fits_either_sign(I.negative(a),q,a,
        Equal.trans(Bool,I.unsigned_lt(q,I.magnitude(a)),Nat.is_lt(A.unsigned(q),Division.absolute(a)),True{},Order.actual_unsigned_lt_is_natural_order(q,I.magnitude(a)),Equal.cong(Cmp,Bool,Cmp.is_lt,Nat.cmp(A.unsigned(q),Division.absolute(a)),LT{},actual)))
    case EQ{}:
      Equal.trans(Bool,I.out_of_range(I.negative(a),q),I.out_of_range(I.negative(a),I.magnitude(a)),False{},
        Equal.cong(V.Int64,Bool,x => I.out_of_range(I.negative(a),x),q,I.magnitude(a),Signed.unsigned_value_is_injective(q,I.magnitude(a),equal_natural_comparison_is_equality(A.unsigned(q),Division.absolute(a),actual))),
        Signed.representable_signed_magnitude_forces_fitting(I.negative(a),I.magnitude(a),a,Product.actual_magnitude_for_product(a)))
    case GT{}: F.absurd_boolean({I.out_of_range(I.negative(a),q) == False{} : Bool},less)

law quotient_within_absolute_dividend_fits_its_sign:
  for +a: V.Int64
  for +q: V.Int64
  for less: {Nat.is_le(A.unsigned(q),Division.absolute(a)) == True{} : Bool}
  {I.out_of_range(I.negative(a),q) == False{} : Bool}
def quotient_within_absolute_dividend_fits_its_sign(a,q,less):
  bounded_quotient_case(Nat.cmp(A.unsigned(q),Division.absolute(a)),a,q,{==},less)

law xor_false_is_identity:
  for +a: Bool
  {Bool.xor(a,False{}) == a : Bool}
def xor_false_is_identity(a):
  match a:
    case False{}: {==}
    case True{}: {==}

type DivisionWitness<-a: V.Int64,-b: V.Int64> is Type:
  DivisionWitness{quotient: V.Int64,remainder: V.Int64,meaning: Division.Meaning<a,b,quotient,remainder>}

def unsigned_result_supplies_representable_division(+a: V.Int64,+b: V.Int64,+nonnegative: {I.negative(b) == False{} : Bool},+nonzero: {I.zero(b) == False{} : Bool},result: I.Division,correct: Unsigned.Euclidean(I.magnitude(a),I.magnitude(b),result)) -> DivisionWitness<a,b>:
  match result correct:
    case I.Division{+uq,+ur} L.Both{+equation,L.Both{small,proper}}:
      +sign = Equal.trans(Bool,Division.quotient_sign(a,b),Bool.xor(I.negative(a),False{}),I.negative(a),Equal.cong(Bool,Bool,s => Bool.xor(I.negative(a),s),I.negative(b),False{},nonnegative),xor_false_is_identity(I.negative(a)))
      +fits = {(%Equal.sym(Bool,Division.quotient_sign(a,b),I.negative(a),sign) : {I.out_of_range(_,uq) == False{} : Bool}
        quotient_within_absolute_dividend_fits_its_sign(a,uq,positive_division_bounds_quotient(Division.absolute(a),Division.absolute(b),A.unsigned(uq),A.unsigned(ur),Zero.nonzero_divisor_has_strictly_positive_magnitude(b,nonzero),equation))) : {I.out_of_range(Division.quotient_sign(a,b),uq) == False{} : Bool}}
      DivisionWitness{I.signed_word(Division.quotient_sign(a,b),uq),I.signed_word(I.negative(a),ur),
        Signing.accepted_unsigned_result_has_signed_meaning(a,b,uq,ur,I.signed_word(Division.quotient_sign(a,b),uq),
          Equal.cong(Bool,Maybe<&2,V.Int64>,overflow => I.checked(overflow,I.signed_word(Division.quotient_sign(a,b),uq)),I.out_of_range(Division.quotient_sign(a,b),uq),False{},fits),nonzero,equation,small,proper)}

law every_positive_divisor_has_a_representable_truncating_division:
  for +a: V.Int64
  for +b: V.Int64
  for nonnegative: {I.negative(b) == False{} : Bool}
  for +nonzero: {I.zero(b) == False{} : Bool}
  DivisionWitness<a,b>
def every_positive_divisor_has_a_representable_truncating_division(a,b,nonnegative,nonzero):
  unsigned_result_supplies_representable_division(a,b,nonnegative,nonzero,I.divide_step(64n,I.magnitude(a),I.magnitude(b),V.Int64{0,0},V.Int64{0,0}),
    Unsigned.actual_unsigned_division(I.magnitude(a),I.magnitude(b),Equal.trans(Bool,I.zero(I.magnitude(b)),I.zero(b),False{},Zero.actual_magnitude_preserves_exact_zero(b),nonzero),Bound.actual_magnitude_word_is_at_most_sign_threshold(b)))
