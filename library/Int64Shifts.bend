# Exact bit-operation links for the actual two-word multiplier.
import Base
import ./Value.bend as V
import ./Int64.bend as I
import ./Int64Proofs.bend as A
import ../contract/Logic.bend as L
import ../proof/Foundations.bend as F
import ../proof/CodecWordsWord.bend as W
import ../proof/CodecSumsBits.bend as S
import ../proof/CodecCounters.bend as N
import ../proof/CodecUTF8Bits.bend as X
import ../proof/Orders.bend as O
import ../proof/CodecAcceptanceTags.bend as Tags

def end_bit(n: Nat, carry: Bool, w: Word(n)) -> Bool:
  match n:
    case 0n: carry
    case 1n+p:
      match w:
        case WCon{b, tail}: end_bit(p, b, tail)

law end_bit_is_top:
  for +n: Nat
  for carry: Bool
  for +w: Word(1n+n)
  {end_bit(1n+n, carry, w) == A.top(1n+n, w) : Bool}
def end_bit_is_top(n, carry, w):
  match n:
    case 0n:
      match w:
        case WCon{b, WNil{}}: {==}
    case 1n+p:
      match w:
        case WCon{b, tail}: end_bit_is_top(p, b, tail)

law shift_is_put_zero:
  for +n: Nat
  for +w: Word(n)
  {Word.shl(n, w) == Word.shl.put(n, False{}, w) : Word(n)}
def shift_is_put_zero(n, w):
  match n:
    case 0n: {==}
    case 1n+p:
      match w:
        case WCon{b, tail}: {==}

law shift_put_blocks:
  for +k: Nat
  for +n: Nat
  for +carry: Bool
  for +lo: Word(k)
  for +hi: Word(n)
  {Word.shl.put(Nat.add(k, n), carry, W.join(k, n, lo, hi)) ==
    W.join(k, n, Word.shl.put(k, carry, lo), Word.shl.put(n, end_bit(k, carry, lo), hi)) : Word(Nat.add(k, n))}
def shift_put_blocks(k, n, carry, lo, hi):
  match k:
    case 0n: {==}
    case 1n+p:
      match lo:
        case WCon{b, tail}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), w => WCon{carry, w},
            Word.shl.put(Nat.add(p, n), b, W.join(p, n, tail, hi)),
            W.join(p, n, Word.shl.put(p, b, tail), Word.shl.put(n, end_bit(p, b, tail), hi)), shift_put_blocks(p, n, b, tail, hi))

law or_zero_right:
  for +n: Nat
  for +w: Word(n)
  {Word.or(n, w, Word.zero(n)) == w : Word(n)}
def or_zero_right(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}: {==}
    case 1n+p:
      match w:
        case WCon{False{}, tail}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.or(p, tail, Word.zero(p)), tail, or_zero_right(p, tail))
        case WCon{True{}, tail}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w}, Word.or(p, tail, Word.zero(p)), tail, or_zero_right(p, tail))

law shifted_low_bit:
  for +n: Nat
  for +w: Word(1n+n)
  for +carry: Bool
  {Word.or(1n+n, Word.shl(1n+n, w), WCon{carry, Word.zero(n)}) == Word.shl.put(1n+n, carry, w) : Word(1n+n)}
def shifted_low_bit(n, w, carry):
  match w:
    case WCon{b, tail}:
      Equal.cong(Word(n), Word(1n+n), w => WCon{carry, w},
        Word.or(n, Word.shl.put(n, b, tail), Word.zero(n)), Word.shl.put(n, b, tail), or_zero_right(n, Word.shl.put(n, b, tail)))

law bits_shl_carry:
  for +hi: Word(32n)
  for +lo: Word(32n)
  for +carry: Bool
  {A.bits(V.Int64{U32.or(U32.shl(U32{hi}), Bool.to_u32(carry)), U32.shl(U32{lo})}) ==
    W.join(32n, 32n, Word.shl(32n, lo), Word.shl.put(32n, carry, hi)) : Word(64n)}
def bits_shl_carry(hi, lo, carry):
  match carry:
    case False{}:
      Equal.cong(Word(32n), Word(64n), w => W.join(32n, 32n, Word.shl(32n, lo), w),
        Word.or(32n, Word.shl(32n, hi), WCon{False{}, Word.zero(31n)}), Word.shl.put(32n, False{}, hi), shifted_low_bit(31n, hi, False{}))
    case True{}:
      Equal.cong(Word(32n), Word(64n), w => W.join(32n, 32n, Word.shl(32n, lo), w),
        Word.or(32n, Word.shl(32n, hi), WCon{True{}, Word.zero(31n)}), Word.shl.put(32n, True{}, hi), shifted_low_bit(31n, hi, True{}))

law shl_is_full_word_shift:
  for +x: V.Int64
  {A.bits(I.shl(x)) == Word.shl(64n, A.bits(x)) : Word(64n)}
def shl_is_full_word_shift(x):
  match x:
    case V.Int64{U32{+hi}, U32{+lo}}:
      %Equal.sym(Bool, U32.is_ge(U32{lo}, 2147483648), end_bit(32n, False{}, lo),
        Equal.trans(Bool, U32.is_ge(U32{lo}, 2147483648), A.top(32n, lo), end_bit(32n, False{}, lo),
          A.sign_threshold_is_top(31n, lo), Equal.sym(Bool, end_bit(32n, False{}, lo), A.top(32n, lo), end_bit_is_top(31n, False{}, lo)))) :
        {A.bits(V.Int64{U32.or(U32.shl(U32{hi}), Bool.to_u32(_)), U32.shl(U32{lo})}) == Word.shl(64n, W.join(32n, 32n, lo, hi)) : Word(64n)}
      Equal.trans(Word(64n),
        A.bits(V.Int64{U32.or(U32.shl(U32{hi}), Bool.to_u32(end_bit(32n, False{}, lo))), U32.shl(U32{lo})}),
        W.join(32n, 32n, Word.shl(32n, lo), Word.shl.put(32n, end_bit(32n, False{}, lo), hi)), Word.shl(64n, W.join(32n, 32n, lo, hi)),
        bits_shl_carry(hi, lo, end_bit(32n, False{}, lo)),
        Equal.trans(Word(64n), W.join(32n, 32n, Word.shl(32n, lo), Word.shl.put(32n, end_bit(32n, False{}, lo), hi)),
          Word.shl.put(64n, False{}, W.join(32n, 32n, lo, hi)), Word.shl(64n, W.join(32n, 32n, lo, hi)),
          (%Equal.sym(Word(32n), Word.shl(32n, lo), Word.shl.put(32n, False{}, lo), shift_is_put_zero(32n, lo)) :
            {W.join(32n, 32n, _, Word.shl.put(32n, end_bit(32n, False{}, lo), hi)) == Word.shl.put(64n, False{}, W.join(32n, 32n, lo, hi)) : Word(64n)}
            Equal.sym(Word(64n), Word.shl.put(64n, False{}, W.join(32n, 32n, lo, hi)),
              W.join(32n, 32n, Word.shl.put(32n, False{}, lo), Word.shl.put(32n, end_bit(32n, False{}, lo), hi)), shift_put_blocks(32n, 32n, False{}, lo, hi))),
          Equal.sym(Word(64n), Word.shl(64n, W.join(32n, 32n, lo, hi)), Word.shl.put(64n, False{}, W.join(32n, 32n, lo, hi)), shift_is_put_zero(64n, W.join(32n, 32n, lo, hi)))))

def insert_top(n: Nat, top: Bool, w: Word(n)) -> Word(1n+n):
  match n:
    case 0n: WCon{top, WNil{}}
    case 1n+p:
      match w:
        case WCon{b, tail}: WCon{b, insert_top(p, top, tail)}

def shr_put(n: Nat, top: Bool, w: Word(n)) -> Word(n):
  match n:
    case 0n: WNil{}
    case 1n+p:
      match w:
        case WCon{b, tail}: insert_top(p, top, tail)

def top_word(+n: Nat, top: Bool) -> Word(1n+n):
  insert_top(n, top, Word.zero(n))

law padding_or_top:
  for +n: Nat
  for +w: Word(n)
  for +top: Bool
  {Word.or(1n+n, Word.shr.pad(n, w), top_word(n, top)) == insert_top(n, top, w) : Word(1n+n)}
def padding_or_top(n, w, top):
  match n:
    case 0n:
      match top:
        case False{}: {==}
        case True{}: {==}
    case 1n+p:
      match w:
        case WCon{False{}, tail}:
          Equal.cong(Word(1n+p), Word(2n+p), w => WCon{False{}, w},
            Word.or(1n+p, Word.shr.pad(p, tail), top_word(p, top)), insert_top(p, top, tail), padding_or_top(p, tail, top))
        case WCon{True{}, tail}:
          Equal.cong(Word(1n+p), Word(2n+p), w => WCon{True{}, w},
            Word.or(1n+p, Word.shr.pad(p, tail), top_word(p, top)), insert_top(p, top, tail), padding_or_top(p, tail, top))

law right_shift_carry:
  for +n: Nat
  for +w: Word(1n+n)
  for +top: Bool
  {Word.or(1n+n, Word.shr(1n+n, w), top_word(n, top)) == shr_put(1n+n, top, w) : Word(1n+n)}
def right_shift_carry(n, w, top):
  match w:
    case WCon{b, tail}: padding_or_top(n, tail, top)

law high_word_low_bit_mask:
  for +bit: Bool
  for +tail: Word(31n)
  {Word.mul(32n, Word.and(32n, WCon{bit, tail}, WCon{True{}, Word.zero(31n)}), A.word(2147483648)) == top_word(31n, bit) : Word(32n)}
def high_word_low_bit_mask(bit, tail):
  match bit:
    case False{}:
      %Equal.sym(Word(31n), Word.and(31n, tail, Word.zero(31n)), Word.zero(31n), W.mask_zero(31n, tail)) :
        {Word.mul(32n, WCon{False{}, _}, A.word(2147483648)) == top_word(31n, False{}) : Word(32n)}
      {==}
    case True{}:
      %Equal.sym(Word(31n), Word.and(31n, tail, Word.zero(31n)), Word.zero(31n), W.mask_zero(31n, tail)) :
        {Word.mul(32n, WCon{True{}, _}, A.word(2147483648)) == top_word(31n, True{}) : Word(32n)}
      {==}

def head_bit(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n: False{}
    case 1n+p:
      match w:
        case WCon{bit, tail}: bit

law padding_join:
  for +k: Nat
  for +n: Nat
  for +lo: Word(k)
  for +hi: Word(1n+n)
  {Word.shr.pad(Nat.add(k, 1n+n), W.join(k, 1n+n, lo, hi)) ==
    W.join(1n+k, 1n+n, insert_top(k, head_bit(1n+n, hi), lo), Word.shr(1n+n, hi)) : Word(1n+Nat.add(k, 1n+n))}
def padding_join(k, n, lo, hi):
  match k:
    case 0n:
      match hi:
        case WCon{b, tail}: {==}
    case 1n+p:
      match lo:
        case WCon{b, tail}:
          Equal.cong(Word(1n+Nat.add(p, 1n+n)), Word(2n+Nat.add(p, 1n+n)), w => WCon{b, w},
            Word.shr.pad(Nat.add(p, 1n+n), W.join(p, 1n+n, tail, hi)),
            W.join(1n+p, 1n+n, insert_top(p, head_bit(1n+n, hi), tail), Word.shr(1n+n, hi)), padding_join(p, n, tail, hi))

law right_shift_blocks:
  for +k: Nat
  for +n: Nat
  for +lo: Word(1n+k)
  for +hi: Word(1n+n)
  {Word.shr(Nat.add(1n+k, 1n+n), W.join(1n+k, 1n+n, lo, hi)) ==
    W.join(1n+k, 1n+n, shr_put(1n+k, head_bit(1n+n, hi), lo), Word.shr(1n+n, hi)) : Word(Nat.add(1n+k, 1n+n))}
def right_shift_blocks(k, n, lo, hi):
  match lo:
    case WCon{b, tail}: padding_join(k, n, tail, hi)

law shr_is_full_word_shift:
  for +x: V.Int64
  {A.bits(I.shr(x)) == Word.shr(64n, A.bits(x)) : Word(64n)}
def shr_is_full_word_shift(x):
  match x:
    case V.Int64{U32{WCon{+bit, +tail}}, U32{+lo}}:
      %Equal.sym(Word(32n),
        Word.mul(32n, Word.and(32n, WCon{bit, tail}, WCon{True{}, Word.zero(31n)}), A.word(2147483648)), top_word(31n, bit), high_word_low_bit_mask(bit, tail)) :
        {W.join(32n, 32n, Word.or(32n, Word.shr(32n, lo), _), Word.shr(32n, WCon{bit, tail})) ==
          Word.shr(64n, W.join(32n, 32n, lo, WCon{bit, tail})) : Word(64n)}
      Equal.trans(Word(64n), W.join(32n, 32n, Word.or(32n, Word.shr(32n, lo), top_word(31n, bit)), Word.shr(32n, WCon{bit, tail})),
        W.join(32n, 32n, shr_put(32n, bit, lo), Word.shr(32n, WCon{bit, tail})),
        Word.shr(64n, W.join(32n, 32n, lo, WCon{bit, tail})),
        Equal.cong(Word(32n), Word(64n), w => W.join(32n, 32n, w, Word.shr(32n, WCon{bit, tail})),
          Word.or(32n, Word.shr(32n, lo), top_word(31n, bit)), shr_put(32n, bit, lo), right_shift_carry(31n, lo, bit)),
        Equal.sym(Word(64n), Word.shr(64n, W.join(32n, 32n, lo, WCon{bit, tail})),
          W.join(32n, 32n, shr_put(32n, bit, lo), Word.shr(32n, WCon{bit, tail})), right_shift_blocks(31n, 31n, lo, WCon{bit, tail})))
