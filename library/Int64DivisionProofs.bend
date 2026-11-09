# Complete correctness of actual signed divmod against the unchanged integer
# specification. The count stays symbolic through the nonzero proof branch;
# the public operation still delegates to exactly 64 restoring steps.
import Base
import ../contract/Logic.bend as L
import ./Value.bend as V
import ./Int64.bend as I
import ./Int64UnsignedDivision.bend as U
import ./Int64MagnitudeBound.bend as Bound
import ./Int64MagnitudeZero.bend as Zero
import ./Int64ZeroDivision.bend as ZeroDivision
import ./Int64DivisionSigning.bend as Sign
import ./Int64DivisionSpec.bend as S

law counted_zero_branch_is_exact:
  for +steps: Nat
  for +a: V.Int64
  for +b: V.Int64
  {I.divide_count(steps,True{},a,b) == None{} : Maybe<&2,I.Division>}
def counted_zero_branch_is_exact(steps,a,b): {==}

law counted_nonzero_branch_is_exact:
  for +steps: Nat
  for +a: V.Int64
  for +b: V.Int64
  {I.divide_count(steps,False{},a,b) == I.signed_division(Bool.xor(I.negative(a),I.negative(b)),I.negative(a),I.divide_step(steps,I.magnitude(a),I.magnitude(b),V.Int64{0,0},V.Int64{0,0})) : Maybe<&2,I.Division>}
def counted_nonzero_branch_is_exact(steps,a,b): {==}

law count64_is_actual_divide_nonzero:
  for +zero: Bool
  for +a: V.Int64
  for +b: V.Int64
  {I.divide_count(64n,zero,a,b) == I.divide_nonzero(zero,a,b) : Maybe<&2,I.Division>}
def count64_is_actual_divide_nonzero(zero,a,b): {==}

def unsigned_result_has_signed_meaning(+a: V.Int64,+b: V.Int64,result: I.Division,
  nonzero: {I.zero(b) == False{} : Bool},correct: U.Euclidean(I.magnitude(a),I.magnitude(b),result)) ->
  S.DivisionCorrect(a,b,I.signed_division(S.quotient_sign(a,b),I.negative(a),result)):
  match result:
    case I.Division{uq,ur}:
      match correct:
        case L.Both{equation,L.Both{small,proper}}:
          Sign.actual_unsigned_division_signing_preserves_complete_euclidean_meaning(a,b,uq,ur,nonzero,equation,small,proper)

# The conditional unsigned theorem is supplied by the proven actual 64-step
# algorithm at the public boundary. No algorithm fact is a public premise.
def division_case(steps: Nat,zero: Bool,+a: V.Int64,+b: V.Int64,+actual: {I.zero(b) == zero : Bool},
  unsigned: {I.zero(b) == False{} : Bool} -> U.Euclidean(I.magnitude(a),I.magnitude(b),I.divide_step(steps,I.magnitude(a),I.magnitude(b),V.Int64{0,0},V.Int64{0,0}))) ->
  S.DivisionCorrect(a,b,I.divide_count(steps,zero,a,b)):
  match zero:
    case True{}: ZeroDivision.zero_divisor_rejection_has_no_mathematical_candidate(a,b,actual)
    case False{}:
      unsigned_result_has_signed_meaning(a,b,I.divide_step(steps,I.magnitude(a),I.magnitude(b),V.Int64{0,0},V.Int64{0,0}),actual,unsigned(actual))

law checked_divmod_is_truncating_integer_division:
  for +a: V.Int64
  for +b: V.Int64
  S.DivisionCorrect(a,b,I.divmod(a,b))
def checked_divmod_is_truncating_integer_division(a,b):
  %count64_is_actual_divide_nonzero(I.zero(b),a,b) : S.DivisionCorrect(a,b,_)
  division_case(64n,I.zero(b),a,b,{==},+nonzero => U.actual_unsigned_division(I.magnitude(a),I.magnitude(b),
    Equal.trans(Bool,I.zero(I.magnitude(b)),I.zero(b),False{},Zero.actual_magnitude_preserves_exact_zero(b),nonzero),Bound.actual_magnitude_word_is_at_most_sign_threshold(b)))
