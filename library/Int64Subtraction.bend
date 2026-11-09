# Total checked signed subtraction against independent Nat-difference integers.
import Base
import ./Int64SubProofs.bend as W
import ./Value.bend as V
import ./Int64.bend as I
import ./Int64Proofs.bend as A
import ../contract/Logic.bend as L
import ../proof/Foundations.bend as F

law wrapping_add_undoes_subtraction:
  for +a: V.Int64
  for +b: V.Int64
  {I.wrapping_add(b, I.wrapping_sub(a, b)) == a : V.Int64}
def wrapping_add_undoes_subtraction(a, b):
  A.bits_injective(I.wrapping_add(b, I.wrapping_sub(a, b)), a,
    Equal.trans(Word(64n), A.bits(I.wrapping_add(b, I.wrapping_sub(a, b))),
      Word.add(64n, A.bits(b), A.bits(I.wrapping_sub(a, b))), A.bits(a),
      A.wrapping_add_is_full_word_add(b, I.wrapping_sub(a, b)),
      Equal.trans(Word(64n), Word.add(64n, A.bits(b), A.bits(I.wrapping_sub(a, b))),
        Word.add(64n, A.bits(b), Word.sub(64n, A.bits(a), A.bits(b))), A.bits(a),
        Equal.cong(Word(64n), Word(64n), w => Word.add(64n, A.bits(b), w), A.bits(I.wrapping_sub(a, b)),
          Word.sub(64n, A.bits(a), A.bits(b)), W.wrapping_sub_is_full_word_sub(a, b)),
        Equal.trans(Word(64n), Word.add(64n, A.bits(b), Word.sub(64n, A.bits(a), A.bits(b))),
          Word.add(64n, Word.sub(64n, A.bits(a), A.bits(b)), A.bits(b)), A.bits(a),
          Word.add_comm(64n, A.bits(b), Word.sub(64n, A.bits(a), A.bits(b))),
          W.word_subtract_then_add(64n, A.bits(a), A.bits(b), True{})))))

law wrapping_subtraction_undoes_add:
  for +b: V.Int64
  for +r: V.Int64
  {I.wrapping_sub(I.wrapping_add(b, r), b) == r : V.Int64}
def wrapping_subtraction_undoes_add(b, r):
  A.bits_injective(I.wrapping_sub(I.wrapping_add(b, r), b), r,
    Equal.trans(Word(64n), A.bits(I.wrapping_sub(I.wrapping_add(b, r), b)),
      Word.sub(64n, A.bits(I.wrapping_add(b, r)), A.bits(b)), A.bits(r),
      W.wrapping_sub_is_full_word_sub(I.wrapping_add(b, r), b),
      Equal.trans(Word(64n), Word.sub(64n, A.bits(I.wrapping_add(b, r)), A.bits(b)),
        Word.sub(64n, Word.add(64n, A.bits(b), A.bits(r)), A.bits(b)), A.bits(r),
        Equal.cong(Word(64n), Word(64n), w => Word.sub(64n, w, A.bits(b)), A.bits(I.wrapping_add(b, r)),
          Word.add(64n, A.bits(b), A.bits(r)), A.wrapping_add_is_full_word_add(b, r)),
        Equal.trans(Word(64n), Word.sub(64n, Word.add(64n, A.bits(b), A.bits(r)), A.bits(b)),
          Word.sub(64n, Word.add(64n, A.bits(r), A.bits(b)), A.bits(b)), A.bits(r),
          Equal.cong(Word(64n), Word(64n), w => Word.sub(64n, w, A.bits(b)), Word.add(64n, A.bits(b), A.bits(r)),
            Word.add(64n, A.bits(r), A.bits(b)), Word.add_comm(64n, A.bits(b), A.bits(r))),
          W.word_add_then_subtract(64n, A.bits(r), A.bits(b), False{})))))

law overflow_sign_equivalence:
  for +a: Bool
  for +b: Bool
  for +r: Bool
  {(Bool.xor(a, b) && Bool.xor(a, r)) == (Bool.not(Bool.xor(b, r)) && Bool.xor(b, a)) : Bool}
def overflow_sign_equivalence(a, b, r):
  match a b r:
    case False{} False{} False{}: {==}
    case False{} False{} True{}: {==}
    case False{} True{} False{}: {==}
    case False{} True{} True{}: {==}
    case True{} False{} False{}: {==}
    case True{} False{} True{}: {==}
    case True{} True{} False{}: {==}
    case True{} True{} True{}: {==}

law subtraction_overflow_is_inverse_addition_overflow:
  for +a: V.Int64
  for +b: V.Int64
  {I.sub_overflow(a, b) == I.add_overflow(b, I.wrapping_sub(a, b)) : Bool}
def subtraction_overflow_is_inverse_addition_overflow(a, b):
  Equal.trans(Bool, I.sub_overflow(a, b),
    Bool.not(Bool.xor(I.negative(b), I.negative(I.wrapping_sub(a, b)))) && Bool.xor(I.negative(b), I.negative(a)),
    I.add_overflow(b, I.wrapping_sub(a, b)),
    overflow_sign_equivalence(I.negative(a), I.negative(b), I.negative(I.wrapping_sub(a, b))),
    Equal.cong(V.Int64, Bool, sum => Bool.not(Bool.xor(I.negative(b), I.negative(I.wrapping_sub(a, b)))) && Bool.xor(I.negative(b), I.negative(sum)),
      a, I.wrapping_add(b, I.wrapping_sub(a, b)),
      Equal.sym(V.Int64, I.wrapping_add(b, I.wrapping_sub(a, b)), a, wrapping_add_undoes_subtraction(a, b))))

# a - b = r means b + r = a in the same independent mathematical integer model.
def IntegerDifference(a: A.Integer, b: A.Integer, r: A.Integer) -> Type:
  A.IntegerSum(b, r, a)

law fitting_subtraction_is_integer_difference:
  for +a: V.Int64
  for +b: V.Int64
  for fits: {I.sub_overflow(a, b) == False{} : Bool}
  IntegerDifference(A.integer(a), A.integer(b), A.integer(I.wrapping_sub(a, b)))
def fitting_subtraction_is_integer_difference(a, b, fits):
  add_fits = Equal.trans(Bool, I.add_overflow(b, I.wrapping_sub(a, b)), I.sub_overflow(a, b), False{},
    Equal.sym(Bool, I.sub_overflow(a, b), I.add_overflow(b, I.wrapping_sub(a, b)), subtraction_overflow_is_inverse_addition_overflow(a, b)), fits)
  %wrapping_add_undoes_subtraction(a, b) :
    A.IntegerSum(A.integer(b), A.integer(I.wrapping_sub(a, b)), A.integer(_))
  A.fitting_add_is_integer_addition(b, I.wrapping_sub(a, b), add_fits)

# Copy only actual equality evidence (Data), never an affine arbitrary integer
# proposition. Both consequences are derived from the same proved residue data.
def sum_details(+a: V.Int64, +b: V.Int64, +r: V.Int64, data: A.ResidueData(a, b, r)) ->
  L.E<{r == I.wrapping_add(a, b) : V.Int64}, {I.add_overflow(a, b) == False{} : Bool}>:
  match data:
    case L.Both{+residue, +coefficients}:
      L.Both{A.candidate_from_residue(a, b, r, L.Both{residue, coefficients}),
        A.fitting_from_residue(a, b, r, L.Both{residue, coefficients})}

def fitting_from_sum_details(+a: V.Int64, +b: V.Int64, +r: V.Int64,
  details: L.E<{a == I.wrapping_add(b, r) : V.Int64}, {I.add_overflow(b, r) == False{} : Bool}>) ->
  {I.sub_overflow(a, b) == False{} : Bool}:
  match details:
    case L.Both{same, fitting}:
      actual_result = Equal.trans(V.Int64, I.wrapping_sub(a, b), I.wrapping_sub(I.wrapping_add(b, r), b), r,
        Equal.cong(V.Int64, V.Int64, sum => I.wrapping_sub(sum, b), a, I.wrapping_add(b, r), same), wrapping_subtraction_undoes_add(b, r))
      Equal.trans(Bool, I.sub_overflow(a, b), I.add_overflow(b, I.wrapping_sub(a, b)), False{},
        subtraction_overflow_is_inverse_addition_overflow(a, b),
        Equal.trans(Bool, I.add_overflow(b, I.wrapping_sub(a, b)), I.add_overflow(b, r), False{},
          Equal.cong(V.Int64, Bool, candidate => I.add_overflow(b, candidate), I.wrapping_sub(a, b), r, actual_result), fitting))

law representable_integer_difference_implies_fitting:
  for +a: V.Int64
  for +b: V.Int64
  for +r: V.Int64
  for exact: IntegerDifference(A.integer(a), A.integer(b), A.integer(r))
  {I.sub_overflow(a, b) == False{} : Bool}
def representable_integer_difference_implies_fitting(a, b, r, exact):
  fitting_from_sum_details(a, b, r, sum_details(b, r, a, A.integer_sum_residues(b, r, a, exact)))

law integer_difference_candidate_is_wrapped:
  for +a: V.Int64
  for +b: V.Int64
  for +r: V.Int64
  for exact: IntegerDifference(A.integer(a), A.integer(b), A.integer(r))
  {r == I.wrapping_sub(a, b) : V.Int64}
def integer_difference_candidate_is_wrapped(a, b, r, exact):
  sum = A.integer_sum_candidate_is_wrapped(b, r, a, exact)
  Equal.sym(V.Int64, I.wrapping_sub(a, b), r,
    Equal.trans(V.Int64, I.wrapping_sub(a, b), I.wrapping_sub(I.wrapping_add(b, r), b), r,
      Equal.cong(V.Int64, V.Int64, value => I.wrapping_sub(value, b), a, I.wrapping_add(b, r), sum), wrapping_subtraction_undoes_add(b, r)))

def SubtractionCorrect(+a: V.Int64, +b: V.Int64, result: Maybe<&2, V.Int64>) -> Type:
  match result:
    case Some{r}: IntegerDifference(A.integer(a), A.integer(b), A.integer(r))
    case None{}: @r: V.Int64 -> IntegerDifference(A.integer(a), A.integer(b), A.integer(r)) -> Empty

def subtraction_case(overflow: Bool, +a: V.Int64, +b: V.Int64,
  actual: {I.sub_overflow(a, b) == overflow : Bool}) -> SubtractionCorrect(a, b, I.checked(overflow, I.wrapping_sub(a, b))):
  match overflow:
    case False{}: fitting_subtraction_is_integer_difference(a, b, actual)
    case True{}:
      r => candidate => F.false_negative_true(
        Equal.trans(Bool, False{}, I.sub_overflow(a, b), True{},
          Equal.sym(Bool, I.sub_overflow(a, b), False{}, representable_integer_difference_implies_fitting(a, b, r, candidate)), actual))

# No arithmetic, result, borrow, overflow, or candidate-validity premises.
law checked_sub_is_integer_subtraction:
  for +a: V.Int64
  for +b: V.Int64
  SubtractionCorrect(a, b, I.sub(a, b))
def checked_sub_is_integer_subtraction(a, b):
  subtraction_case(I.sub_overflow(a, b), a, b, {==})
