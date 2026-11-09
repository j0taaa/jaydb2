# Actual multiplier flags linked to word order, parity and unbounded values.
import Base
import ./Int64Shifts.bend as W
import ./Int64ShiftArithmetic.bend as T
import ./Value.bend as V
import ./Int64.bend as I
import ./Int64Proofs.bend as A
import ../contract/Logic.bend as L
import ../proof/Foundations.bend as F
import ../proof/CodecWordsWord.bend as Words
import ../proof/CodecSumsBits.bend as S
import ../proof/CodecCounters.bend as N
import ../proof/CodecUTF8Bits.bend as X
import ../proof/Orders.bend as O
import ../proof/CodecAcceptanceTags.bend as Tags

law priority_is_unsigned_lt:
  for +high: Cmp
  for +low: Cmp
  {Cmp.is_lt(O.priority(high, low)) == (Cmp.is_lt(high) || (Cmp.is_eq(high) && Cmp.is_lt(low))) : Bool}
def priority_is_unsigned_lt(high, low):
  match high:
    case LT{}: {==}
    case EQ{}: {==}
    case GT{}: {==}

law unsigned_lt_is_word_order:
  for +a: V.Int64
  for +b: V.Int64
  {I.unsigned_lt(a, b) == Cmp.is_lt(Word.cmp(64n, A.bits(a), A.bits(b))) : Bool}
def unsigned_lt_is_word_order(a, b):
  match a b:
    case V.Int64{U32{+ah}, U32{+al}} V.Int64{U32{+bh}, U32{+bl}}:
      Equal.sym(Bool, Cmp.is_lt(Word.cmp(64n, Words.join(32n, 32n, al, ah), Words.join(32n, 32n, bl, bh))),
        Cmp.is_lt(Word.cmp(32n, ah, bh)) || (Cmp.is_eq(Word.cmp(32n, ah, bh)) && Cmp.is_lt(Word.cmp(32n, al, bl))),
        Equal.trans(Bool, Cmp.is_lt(Word.cmp(64n, Words.join(32n, 32n, al, ah), Words.join(32n, 32n, bl, bh))),
          Cmp.is_lt(O.priority(Word.cmp(32n, ah, bh), Word.cmp(32n, al, bl))),
          Cmp.is_lt(Word.cmp(32n, ah, bh)) || (Cmp.is_eq(Word.cmp(32n, ah, bh)) && Cmp.is_lt(Word.cmp(32n, al, bl))),
          Equal.cong(Cmp, Bool, Cmp.is_lt, Word.cmp(64n, Words.join(32n, 32n, al, ah), Words.join(32n, 32n, bl, bh)),
            O.priority(Word.cmp(32n, ah, bh), Word.cmp(32n, al, bl)), X.compare_blocks(32n, 32n, al, bl, ah, bh)),
          priority_is_unsigned_lt(Word.cmp(32n, ah, bh), Word.cmp(32n, al, bl))))

law odd_is_low_bit:
  for +x: V.Int64
  {I.odd(x) == W.head_bit(64n, A.bits(x)) : Bool}
def odd_is_low_bit(x):
  match x:
    case V.Int64{U32{hi}, U32{WCon{False{}, +tail}}}:
      %Equal.sym(Word(31n), Word.and(31n, tail, Word.zero(31n)), Word.zero(31n), Words.mask_zero(31n, tail)) :
        {U32.is_eq(U32{WCon{False{}, _}}, 1) == False{} : Bool}
      {==}
    case V.Int64{U32{hi}, U32{WCon{True{}, +tail}}}:
      %Equal.sym(Word(31n), Word.and(31n, tail, Word.zero(31n)), Word.zero(31n), Words.mask_zero(31n, tail)) :
        {U32.is_eq(U32{WCon{True{}, _}}, 1) == True{} : Bool}
      {==}

law right_shift_natural:
  for +x: V.Int64
  {A.unsigned(x) == A.place(I.odd(x), A.unsigned(I.shr(x))) : Nat}
def right_shift_natural(x):
  Equal.trans(Nat, A.unsigned(x), A.place(W.head_bit(64n, A.bits(x)), Word.to_nat(64n, Word.shr(64n, A.bits(x)))),
    A.place(I.odd(x), A.unsigned(I.shr(x))), T.right_shift_word_natural(63n, A.bits(x)),
    Equal.trans(Nat, A.place(W.head_bit(64n, A.bits(x)), Word.to_nat(64n, Word.shr(64n, A.bits(x)))),
      A.place(W.head_bit(64n, A.bits(x)), A.unsigned(I.shr(x))), A.place(I.odd(x), A.unsigned(I.shr(x))),
      Equal.cong(Word(64n), Nat, w => A.place(W.head_bit(64n, A.bits(x)), Word.to_nat(64n, w)),
        Word.shr(64n, A.bits(x)), A.bits(I.shr(x)), Equal.sym(Word(64n), A.bits(I.shr(x)), Word.shr(64n, A.bits(x)), W.shr_is_full_word_shift(x))),
      Equal.cong(Bool, Nat, bit => A.place(bit, A.unsigned(I.shr(x))), W.head_bit(64n, A.bits(x)), I.odd(x),
        Equal.sym(Bool, I.odd(x), W.head_bit(64n, A.bits(x)), odd_is_low_bit(x)))))

law unsigned_add_carry_is_guard:
  for +accumulator: V.Int64
  for +a: V.Int64
  {I.unsigned_lt(I.wrapping_add(accumulator, a), accumulator) == S.carry(64n, A.bits(accumulator), A.bits(a), False{}) : Bool}
def unsigned_add_carry_is_guard(accumulator, a):
  Equal.trans(Bool, I.unsigned_lt(I.wrapping_add(accumulator, a), accumulator),
    Cmp.is_lt(Word.cmp(64n, A.bits(I.wrapping_add(accumulator, a)), A.bits(accumulator))),
    S.carry(64n, A.bits(accumulator), A.bits(a), False{}), unsigned_lt_is_word_order(I.wrapping_add(accumulator, a), accumulator),
    Equal.trans(Bool, Cmp.is_lt(Word.cmp(64n, A.bits(I.wrapping_add(accumulator, a)), A.bits(accumulator))),
      Cmp.is_lt(Word.cmp(64n, Word.add(64n, A.bits(accumulator), A.bits(a)), A.bits(accumulator))),
      S.carry(64n, A.bits(accumulator), A.bits(a), False{}),
      Equal.cong(Word(64n), Bool, w => Cmp.is_lt(Word.cmp(64n, w, A.bits(accumulator))),
        A.bits(I.wrapping_add(accumulator, a)), Word.add(64n, A.bits(accumulator), A.bits(a)), A.wrapping_add_is_full_word_add(accumulator, a)),
      Equal.sym(Bool, S.carry(64n, A.bits(accumulator), A.bits(a), False{}),
        Cmp.is_lt(Word.cmp(64n, Word.add(64n, A.bits(accumulator), A.bits(a)), A.bits(accumulator))),
        S.carry_equivalent_comparison(64n, A.bits(accumulator), A.bits(a), False{}))))

law zero_guard_is_sound:
  for +x: V.Int64
  for +zero: {I.zero(x) == True{} : Bool}
  {x == V.Int64{0, 0} : V.Int64}
def zero_guard_is_sound(x, zero):
  match x:
    case V.Int64{+hi, +lo}:
      Equal.trans(V.Int64, V.Int64{hi, lo}, V.Int64{0, lo}, V.Int64{0, 0},
        Equal.cong(U32, V.Int64, h => V.Int64{h, lo}, hi, 0,
          N.equality_u32(hi, 0, F.and_boolean_left(U32.is_zero(hi), U32.is_zero(lo), zero))),
        Equal.cong(U32, V.Int64, l => V.Int64{0, l}, lo, 0,
          N.equality_u32(lo, 0, F.and_boolean_right(U32.is_zero(hi), U32.is_zero(lo), zero))))

law unsigned_zero_is_zero_word:
  for +x: V.Int64
  for zero: {A.unsigned(x) == 0n : Nat}
  {x == V.Int64{0, 0} : V.Int64}
def unsigned_zero_is_zero_word(x, zero):
  A.bits_injective(x, V.Int64{0, 0}, Tags.word_to_nat_injective(64n, A.bits(x), A.bits(V.Int64{0, 0}), zero))

law unsigned_zero_forces_zero_guard:
  for +x: V.Int64
  for zero: {A.unsigned(x) == 0n : Nat}
  {I.zero(x) == True{} : Bool}
def unsigned_zero_forces_zero_guard(x, zero):
  Equal.cong(V.Int64, Bool, I.zero, x, V.Int64{0, 0}, unsigned_zero_is_zero_word(x, zero))

type Positive<-x: V.Int64> is Type:
  Positive{predecessor: Nat, measure: {A.unsigned(x) == 1n+predecessor : Nat}}

def positive_case(natural: Nat, +x: V.Int64, same: {A.unsigned(x) == natural : Nat},
  nonzero: {I.zero(x) == False{} : Bool}) -> Positive<x>:
  match natural:
    case 0n:
      L.ex_false(Positive<x>, F.false_negative_true(Equal.trans(Bool, False{}, I.zero(x), True{},
        Equal.sym(Bool, I.zero(x), False{}, nonzero), unsigned_zero_forces_zero_guard(x, same))))
    case 1n+p: Positive{p, same}

law nonzero_has_positive_measure:
  for +x: V.Int64
  for nonzero: {I.zero(x) == False{} : Bool}
  Positive<x>
def nonzero_has_positive_measure(x, nonzero):
  positive_case(A.unsigned(x), x, {==}, nonzero)
