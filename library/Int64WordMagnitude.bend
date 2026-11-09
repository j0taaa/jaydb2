# Symbolic-width arithmetic avoids ever evaluating a unary 2^64 constant.
import Base
import ./Int64Proofs.bend as A
import ./Int64SubProofs.bend as Sub
import ../proof/CodecSumsBits.bend as S
import ../proof/Foundations.bend as F
import ./Int64MagnitudeCore.bend as M


def integer(+n: Nat, +w: Word(n)) -> A.Integer:
  A.Integer{Word.to_nat(n, w), A.spill(n, A.top(n, w))}

def opposite(+n: Nat, w: Word(n)) -> Word(n):
  Word.sub(n, Word.zero(n), w)

def magnitude(+n: Nat, +w: Word(n)) -> Word(n):
  Bool.pick(Word(n), A.top(n, w), opposite(n, w), w)

law word_zero_has_zero_value:
  for n: Nat
  {Word.to_nat(n, Word.zero(n)) == 0n : Nat}
def word_zero_has_zero_value(n):
  match n:
    case 0n: {==}
    case 1n+p:
      Equal.cong(Nat, Nat, Nat.double, Word.to_nat(p, Word.zero(p)), 0n, word_zero_has_zero_value(p))

law opposite_wraps_sum_to_zero:
  for +n: Nat
  for +w: Word(n)
  {Word.add(n, w, opposite(n, w)) == Word.zero(n) : Word(n)}
def opposite_wraps_sum_to_zero(n, w):
  Equal.trans(Word(n), Word.add(n, w, opposite(n, w)), Word.add(n, opposite(n, w), w), Word.zero(n),
    Word.add_comm(n, w, opposite(n, w)), Sub.word_subtract_then_add(n, Word.zero(n), w, True{}))

law negative_opposite_unsigned_sum_is_radix:
  for +n: Nat
  for +w: Word(1n+n)
  for top: {A.top(1n+n, w) == True{} : Bool}
  {Nat.add(Word.to_nat(1n+n, w), Word.to_nat(1n+n, opposite(1n+n, w))) == A.modulus(1n+n) : Nat}
def negative_opposite_unsigned_sum_is_radix(n, w, top):
  +zero_sum = opposite_wraps_sum_to_zero(1n+n, w)
  +carry = Equal.trans(Bool, S.carry(1n+n, w, opposite(1n+n, w), False{}),
    Cmp.is_lt(Word.cmp(1n+n, Word.add(1n+n, w, opposite(1n+n, w)), w)), True{},
    S.carry_equivalent_comparison(1n+n, w, opposite(1n+n, w), False{}),
    Equal.trans(Bool, Cmp.is_lt(Word.cmp(1n+n, Word.add(1n+n, w, opposite(1n+n, w)), w)),
      Cmp.is_lt(Word.cmp(1n+n, Word.zero(1n+n), w)), True{},
      Equal.cong(Word(1n+n), Bool, z => Cmp.is_lt(Word.cmp(1n+n, z, w)), Word.add(1n+n, w, opposite(1n+n, w)), Word.zero(1n+n), zero_sum),
      M.top_set_word_exceeds_zero(n, w, top)))
  Equal.trans(Nat, Nat.add(Word.to_nat(1n+n, w), Word.to_nat(1n+n, opposite(1n+n, w))),
    Nat.add(Word.to_nat(1n+n, w), Nat.add(Word.to_nat(1n+n, opposite(1n+n, w)), 0n)), A.modulus(1n+n),
    Equal.cong(Nat, Nat, value => Nat.add(Word.to_nat(1n+n, w), value), Word.to_nat(1n+n, opposite(1n+n, w)),
      Nat.add(Word.to_nat(1n+n, opposite(1n+n, w)), 0n), Equal.sym(Nat, Nat.add(Word.to_nat(1n+n, opposite(1n+n, w)), 0n),
        Word.to_nat(1n+n, opposite(1n+n, w)), A.add_zero_right(Word.to_nat(1n+n, opposite(1n+n, w))))),
    Equal.trans(Nat, Nat.add(Word.to_nat(1n+n, w), Nat.add(Word.to_nat(1n+n, opposite(1n+n, w)), 0n)),
      Nat.add(Word.to_nat(1n+n, Word.add(1n+n, w, opposite(1n+n, w))), A.spill(1n+n, S.carry(1n+n, w, opposite(1n+n, w), False{}))),
      A.modulus(1n+n), A.adc_natural(1n+n, w, opposite(1n+n, w), False{}),
      Equal.trans(Nat, Nat.add(Word.to_nat(1n+n, Word.add(1n+n, w, opposite(1n+n, w))), A.spill(1n+n, S.carry(1n+n, w, opposite(1n+n, w), False{}))),
        Nat.add(Word.to_nat(1n+n, Word.zero(1n+n)), A.spill(1n+n, S.carry(1n+n, w, opposite(1n+n, w), False{}))), A.modulus(1n+n),
        Equal.cong(Word(1n+n), Nat, z => Nat.add(Word.to_nat(1n+n, z), A.spill(1n+n, S.carry(1n+n, w, opposite(1n+n, w), False{}))),
          Word.add(1n+n, w, opposite(1n+n, w)), Word.zero(1n+n), zero_sum),
        Equal.trans(Nat, Nat.add(Word.to_nat(1n+n, Word.zero(1n+n)), A.spill(1n+n, S.carry(1n+n, w, opposite(1n+n, w), False{}))),
          A.spill(1n+n, S.carry(1n+n, w, opposite(1n+n, w), False{})), A.modulus(1n+n),
          Equal.cong(Nat, Nat, z => Nat.add(z, A.spill(1n+n, S.carry(1n+n, w, opposite(1n+n, w), False{}))), Word.to_nat(1n+n, Word.zero(1n+n)), 0n, word_zero_has_zero_value(1n+n)),
          Equal.cong(Bool, Nat, c => A.spill(1n+n, c), S.carry(1n+n, w, opposite(1n+n, w), False{}), True{}, carry)))))

def absolute_case(+n: Nat, sign: Bool, +w: Word(1n+n), +actual: {A.top(1n+n, w) == sign : Bool}) ->
  M.IntegerEqual(integer(1n+n, w), M.sign_integer(sign, Word.to_nat(1n+n, Bool.pick(Word(1n+n), sign, opposite(1n+n, w), w)))):
  match sign:
    case False{}:
      %Equal.sym(Bool, A.top(1n+n, w), False{}, actual) :
        M.IntegerEqual(A.Integer{Word.to_nat(1n+n, w), A.spill(1n+n, _)}, M.sign_integer(False{}, Word.to_nat(1n+n, w)))
      {==}
    case True{}:
      %Equal.sym(Bool, A.top(1n+n, w), True{}, actual) :
        M.IntegerEqual(A.Integer{Word.to_nat(1n+n, w), A.spill(1n+n, _)}, M.sign_integer(True{}, Word.to_nat(1n+n, opposite(1n+n, w))))
      negative_opposite_unsigned_sum_is_radix(n, w, actual)

law word_magnitude_is_unsigned_absolute_value:
  for +n: Nat
  for +w: Word(1n+n)
  M.IntegerEqual(integer(1n+n, w), M.sign_integer(A.top(1n+n, w), Word.to_nat(1n+n, magnitude(1n+n, w))))
def word_magnitude_is_unsigned_absolute_value(n, w):
  absolute_case(n, A.top(1n+n, w), w, {==})
