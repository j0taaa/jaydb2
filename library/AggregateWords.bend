# Actual checked-add symmetry and uniqueness of the existing signed word model.
import Base
import ./AggregateModel.bend as M
import ./Value.bend as V
import ./Int64.bend as I
import ./Int64Proofs.bend as A
import ./Int64IntegerProduct.bend as P
import ./Int64SignedMagnitude.bend as Signed

law overflow_boolean_symmetry:
  for +a: Bool
  for +b: Bool
  for +r: Bool
  {Bool.not(Bool.xor(a,b)) && Bool.xor(a,r) == Bool.not(Bool.xor(b,a)) && Bool.xor(b,r) : Bool}
def overflow_boolean_symmetry(a,b,r):
  match a b:
    case False{} False{}: {==}
    case False{} True{}: {==}
    case True{} False{}: {==}
    case True{} True{}: {==}

law actual_checked_add_commutes:
  for +a: V.Int64
  for +b: V.Int64
  {I.add(a,b) == I.add(b,a) : Maybe<&2,V.Int64>}
def actual_checked_add_commutes(a,b):
  Equal.trans(Maybe<&2,V.Int64>,I.add(a,b),I.checked(I.add_overflow(b,a),I.wrapping_add(a,b)),I.add(b,a),
    Equal.cong(Bool,Maybe<&2,V.Int64>,overflow => I.checked(overflow,I.wrapping_add(a,b)),I.add_overflow(a,b),I.add_overflow(b,a),
      Equal.trans(Bool,I.add_overflow(a,b),Bool.not(Bool.xor(I.negative(b),I.negative(a))) && Bool.xor(I.negative(b),I.negative(I.wrapping_add(a,b))),I.add_overflow(b,a),
        overflow_boolean_symmetry(I.negative(a),I.negative(b),I.negative(I.wrapping_add(a,b))),
        Equal.cong(V.Int64,Bool,r => Bool.not(Bool.xor(I.negative(b),I.negative(a))) && Bool.xor(I.negative(b),I.negative(r)),I.wrapping_add(a,b),I.wrapping_add(b,a),Signed.wrapping_add_commutes(a,b)))),
    Equal.cong(V.Int64,Maybe<&2,V.Int64>,r => I.checked(I.add_overflow(b,a),r),I.wrapping_add(a,b),I.wrapping_add(b,a),Signed.wrapping_add_commutes(a,b)))

law integer_interpretation_is_injective:
  for +a: V.Int64
  for +b: V.Int64
  for same: M.EqualInteger(A.integer(a),A.integer(b))
  {a == b : V.Int64}
def integer_interpretation_is_injective(a,b,same):
  Equal.trans(V.Int64,a,I.wrapping_add(V.Int64{0,0},a),b,
    A.integer_sum_candidate_is_wrapped(V.Int64{0,0},a,a,P.integer_equal_reflexive(A.integer(a))),
    Equal.sym(V.Int64,b,I.wrapping_add(V.Int64{0,0},a),A.integer_sum_candidate_is_wrapped(V.Int64{0,0},a,b,same)))
