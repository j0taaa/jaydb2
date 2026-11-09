# Actual two-U32 unsigned magnitude linked to the symbolic-width proof.
import Base
import ./Int64Proofs.bend as A
import ./Int64SubProofs.bend as Sub
import ./Int64.bend as I
import ./Value.bend as V
import ./Int64MagnitudeCore.bend as M
import ./Int64WordMagnitude.bend as W
import ./Int64RangeBits.bend as Bits

def IntegerEqual(a: A.Integer, b: A.Integer) -> Type:
  M.IntegerEqual(a, b)

def sign_integer(sign: Bool, value: Nat) -> A.Integer:
  M.sign_integer(sign, value)

law bits_of_chosen_word:
  for +choice: Bool
  for +a: V.Int64
  for +b: V.Int64
  {A.bits(Bool.pick(V.Int64, choice, a, b)) == Bool.pick(Word(64n), choice, A.bits(a), A.bits(b)) : Word(64n)}
def bits_of_chosen_word(choice, a, b):
  match choice:
    case False{}: {==}
    case True{}: {==}

law actual_magnitude_bits_are_word_magnitude:
  for +x: V.Int64
  {A.bits(I.magnitude(x)) == W.magnitude(64n, A.bits(x)) : Word(64n)}
def actual_magnitude_bits_are_word_magnitude(x):
  Equal.trans(Word(64n), A.bits(I.magnitude(x)), Bool.pick(Word(64n), I.negative(x), A.bits(Bits.opposite(x)), A.bits(x)), W.magnitude(64n, A.bits(x)),
    bits_of_chosen_word(I.negative(x), Bits.opposite(x), x),
    Equal.trans(Word(64n), Bool.pick(Word(64n), I.negative(x), A.bits(Bits.opposite(x)), A.bits(x)),
      Bool.pick(Word(64n), A.top(64n, A.bits(x)), A.bits(Bits.opposite(x)), A.bits(x)), W.magnitude(64n, A.bits(x)),
      Equal.cong(Bool, Word(64n), sign => Bool.pick(Word(64n), sign, A.bits(Bits.opposite(x)), A.bits(x)),
        I.negative(x), A.top(64n, A.bits(x)), A.negative_is_sign_bit(x)),
      Equal.cong(Word(64n), Word(64n), negated => Bool.pick(Word(64n), A.top(64n, A.bits(x)), negated, A.bits(x)),
        A.bits(Bits.opposite(x)), W.opposite(64n, A.bits(x)), Sub.wrapping_sub_is_full_word_sub(V.Int64{0, 0}, x))))

law actual_magnitude_is_unsigned_absolute_value:
  for +x: V.Int64
  IntegerEqual(A.integer(x), sign_integer(I.negative(x), A.unsigned(I.magnitude(x))))
def actual_magnitude_is_unsigned_absolute_value(x):
  %Equal.sym(Bool, I.negative(x), A.top(64n, A.bits(x)), A.negative_is_sign_bit(x)) :
    IntegerEqual(A.integer(x), sign_integer(_, A.unsigned(I.magnitude(x))))
  %Equal.sym(Word(64n), A.bits(I.magnitude(x)), W.magnitude(64n, A.bits(x)), actual_magnitude_bits_are_word_magnitude(x)) :
    IntegerEqual(A.integer(x), sign_integer(A.top(64n, A.bits(x)), Word.to_nat(64n, _)))
  W.word_magnitude_is_unsigned_absolute_value(63n, A.bits(x))
