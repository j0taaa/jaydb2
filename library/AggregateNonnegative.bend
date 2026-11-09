# Representable nonnegative integers retain their exact natural magnitude and
# have representable predecessors. This closes count completeness without a
# materialized 2^63 unary constant or assumed increment/overflow fact.
import Base
import ./AggregateModel.bend as M
import ./AggregateAddition.bend as Bridge
import ./Value.bend as V
import ./Int64.bend as I
import ./Int64Proofs.bend as A
import ./Int64Subtraction.bend as Sub
import ./Int64IntegerProduct.bend as P
import ./Int64IntegerAddition.bend as Add
import ../proof/Foundations.bend as F

law bounded_nonnegative_sign_is_clear:
  for +width: Nat
  for +unsigned: Nat
  for +natural: Nat
  for +sign: Bool
  for bounded: A.Bound<width,unsigned>
  for exact: {Nat.add(unsigned,0n) == Nat.add(natural,A.spill(width,sign)) : Nat}
  {sign == False{} : Bool}
def bounded_nonnegative_sign_is_clear(width,unsigned,natural,sign,bounded,exact):
  match sign:
    case False{}: {==}
    case True{}:
      F.absurd_boolean({True{} == False{} : Bool},A.contradict_radix_gap(width,unsigned,natural,bounded,
        Equal.trans(Nat,unsigned,Nat.add(unsigned,0n),Nat.add(natural,A.modulus(width)),Equal.sym(Nat,Nat.add(unsigned,0n),unsigned,A.add_zero_right(unsigned)),exact)))

law nonnegative_word_has_clear_sign:
  for +word: V.Int64
  for +natural: Nat
  for exact: M.EqualInteger(A.integer(word),A.Integer{natural,0n})
  {I.negative(word) == False{} : Bool}
def nonnegative_word_has_clear_sign(word,natural,exact):
  Equal.trans(Bool,I.negative(word),A.top(64n,A.bits(word)),False{},A.negative_is_sign_bit(word),
    bounded_nonnegative_sign_is_clear(64n,A.unsigned(word),natural,A.top(64n,A.bits(word)),A.word_value_is_bounded(64n,A.bits(word)),exact))

law nonnegative_word_has_exact_unsigned_value:
  for +word: V.Int64
  for +natural: Nat
  for +exact: M.EqualInteger(A.integer(word),A.Integer{natural,0n})
  {A.unsigned(word) == natural : Nat}
def nonnegative_word_has_exact_unsigned_value(word,natural,exact):
  clear = Equal.trans(Bool,A.top(64n,A.bits(word)),I.negative(word),False{},Equal.sym(Bool,I.negative(word),A.top(64n,A.bits(word)),A.negative_is_sign_bit(word)),nonnegative_word_has_clear_sign(word,natural,exact))
  A.add_right_cancel(0n,A.unsigned(word),natural,Equal.trans(Nat,Nat.add(A.unsigned(word),0n),Nat.add(natural,A.spill(64n,A.top(64n,A.bits(word)))),Nat.add(natural,0n),exact,
    Equal.cong(Bool,Nat,sign => Nat.add(natural,A.spill(64n,sign)),A.top(64n,A.bits(word)),False{},clear)))

law subtracting_one_from_nonnegative_word_fits:
  for +word: V.Int64
  for clear: {I.negative(word) == False{} : Bool}
  {I.sub_overflow(word,V.Int64{0,1}) == False{} : Bool}
def subtracting_one_from_nonnegative_word_fits(word,clear):
  Equal.cong(Bool,Bool,sign => Bool.xor(sign,False{}) && Bool.xor(sign,I.negative(I.wrapping_sub(word,V.Int64{0,1}))),I.negative(word),False{},clear)

law cancel_positive_one:
  for +integer: A.Integer
  for +natural: Nat
  for exact: P.IntegerEqual(Add.add(A.Integer{1n,0n},integer),A.Integer{1n+natural,0n})
  M.EqualInteger(integer,A.Integer{natural,0n})
def cancel_positive_one(integer,natural,exact):
  match integer:
    case A.Integer{+positive,+negative}:
      A.add_left_cancel(1n,Nat.add(positive,0n),Nat.add(natural,negative),exact)

law nonnegative_predecessor_is_represented_by_actual_subtraction:
  for +word: V.Int64
  for +natural: Nat
  for +exact: M.EqualInteger(A.integer(word),A.Integer{1n+natural,0n})
  M.EqualInteger(A.integer(I.wrapping_sub(word,V.Int64{0,1})),A.Integer{natural,0n})
def nonnegative_predecessor_is_represented_by_actual_subtraction(word,natural,exact):
  cancel_positive_one(A.integer(I.wrapping_sub(word,V.Int64{0,1})),natural,
    P.integer_equal_transitive(Add.add(A.integer(V.Int64{0,1}),A.integer(I.wrapping_sub(word,V.Int64{0,1}))),A.integer(word),A.Integer{1n+natural,0n},
      Bridge.sum_equation_to_product_equality(A.integer(V.Int64{0,1}),A.integer(I.wrapping_sub(word,V.Int64{0,1})),A.integer(word),
        Sub.fitting_subtraction_is_integer_difference(word,V.Int64{0,1},subtracting_one_from_nonnegative_word_fits(word,nonnegative_word_has_clear_sign(word,1n+natural,exact)))),
      M.equality_to_integer_product_model(A.integer(word),A.Integer{1n+natural,0n},exact)))
