# Complete signed subtraction, reusing independently proved integer addition.
# All implementation links are proved from the actual two-word operations.
import Base
import ./Value.bend as V
import ./Int64.bend as I
import ./Int64Proofs.bend as A
import ../contract/Logic.bend as L
import ../proof/Foundations.bend as F
import ../proof/CodecSumsBits.bend as S
import ../proof/CodecWordsWord.bend as W
import ../proof/CodecCounters.bend as N

law word_add_then_subtract:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +c: Bool
  {Word.adc(n, Word.adc(n, a, b, False{}, c), b, True{}, Bool.not(c)) == a : Word(n)}
def word_add_then_subtract(n, a, b, c):
  match n:
    case 0n:
      match a:
        case WNil{}: {==}
    case 1n+p:
      match a b c:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            Word.adc(p, Word.adc(p, at, bt, False{}, False{}), bt, True{}, True{}), at,
            word_add_then_subtract(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            Word.adc(p, Word.adc(p, at, bt, False{}, False{}), bt, True{}, True{}), at,
            word_add_then_subtract(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            Word.adc(p, Word.adc(p, at, bt, False{}, False{}), bt, True{}, True{}), at,
            word_add_then_subtract(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            Word.adc(p, Word.adc(p, at, bt, False{}, True{}), bt, True{}, False{}), at,
            word_add_then_subtract(p, at, bt, True{}))
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w},
            Word.adc(p, Word.adc(p, at, bt, False{}, False{}), bt, True{}, True{}), at,
            word_add_then_subtract(p, at, bt, False{}))
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w},
            Word.adc(p, Word.adc(p, at, bt, False{}, True{}), bt, True{}, False{}), at,
            word_add_then_subtract(p, at, bt, True{}))
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w},
            Word.adc(p, Word.adc(p, at, bt, False{}, True{}), bt, True{}, False{}), at,
            word_add_then_subtract(p, at, bt, True{}))
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w},
            Word.adc(p, Word.adc(p, at, bt, False{}, True{}), bt, True{}, False{}), at,
            word_add_then_subtract(p, at, bt, True{}))
law word_subtract_then_add:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +c: Bool
  {Word.adc(n, Word.adc(n, a, b, True{}, c), b, False{}, Bool.not(c)) == a : Word(n)}
def word_subtract_then_add(n, a, b, c):
  match n:
    case 0n:
      match a:
        case WNil{}: {==}
    case 1n+p:
      match a b c:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            Word.adc(p, Word.adc(p, at, bt, True{}, False{}), bt, False{}, True{}), at,
            word_subtract_then_add(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            Word.adc(p, Word.adc(p, at, bt, True{}, True{}), bt, False{}, False{}), at,
            word_subtract_then_add(p, at, bt, True{}))
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            Word.adc(p, Word.adc(p, at, bt, True{}, False{}), bt, False{}, True{}), at,
            word_subtract_then_add(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            Word.adc(p, Word.adc(p, at, bt, True{}, False{}), bt, False{}, True{}), at,
            word_subtract_then_add(p, at, bt, False{}))
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w},
            Word.adc(p, Word.adc(p, at, bt, True{}, True{}), bt, False{}, False{}), at,
            word_subtract_then_add(p, at, bt, True{}))
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w},
            Word.adc(p, Word.adc(p, at, bt, True{}, True{}), bt, False{}, False{}), at,
            word_subtract_then_add(p, at, bt, True{}))
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w},
            Word.adc(p, Word.adc(p, at, bt, True{}, False{}), bt, False{}, True{}), at,
            word_subtract_then_add(p, at, bt, False{}))
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w},
            Word.adc(p, Word.adc(p, at, bt, True{}, True{}), bt, False{}, False{}), at,
            word_subtract_then_add(p, at, bt, True{}))

def carry_order(carry: Bool, order: Cmp) -> Bool:
  match order:
    case LT{}: False{}
    case EQ{}: carry
    case GT{}: True{}

law carry_order_bit:
  for +order: Cmp
  for +a: Bool
  for +b: Bool
  for +c: Bool
  {carry_order(S.bit_carry(a, Bool.not(b), c), order) == carry_order(c, Word.cmp.fin(a, b, order)) : Bool}
def carry_order_bit(order, a, b, c):
  match order:
    case LT{}: {==}
    case GT{}: {==}
    case EQ{}:
      match a b c:
        case False{} False{} False{}: {==}
        case False{} False{} True{}: {==}
        case False{} True{} False{}: {==}
        case False{} True{} True{}: {==}
        case True{} False{} False{}: {==}
        case True{} False{} True{}: {==}
        case True{} True{} False{}: {==}
        case True{} True{} True{}: {==}

law subtraction_carry_reflects_comparison:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +c: Bool
  {S.carry(n, a, Word.not(n, b), c) == carry_order(c, Word.cmp(n, a, b)) : Bool}
def subtraction_carry_reflects_comparison(n, a, b, c):
  match n:
    case 0n: {==}
    case 1n+p:
      match a b c:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          Equal.trans(Bool, S.carry(p, at, Word.not(p, bt), False{}), carry_order(False{}, Word.cmp(p, at, bt)),
            carry_order(False{}, Word.cmp.fin(False{}, False{}, Word.cmp(p, at, bt))),
            subtraction_carry_reflects_comparison(p, at, bt, False{}),
            carry_order_bit(Word.cmp(p, at, bt), False{}, False{}, False{}))
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          Equal.trans(Bool, S.carry(p, at, Word.not(p, bt), True{}), carry_order(True{}, Word.cmp(p, at, bt)),
            carry_order(True{}, Word.cmp.fin(False{}, False{}, Word.cmp(p, at, bt))),
            subtraction_carry_reflects_comparison(p, at, bt, True{}),
            carry_order_bit(Word.cmp(p, at, bt), False{}, False{}, True{}))
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          Equal.trans(Bool, S.carry(p, at, Word.not(p, bt), False{}), carry_order(False{}, Word.cmp(p, at, bt)),
            carry_order(False{}, Word.cmp.fin(False{}, True{}, Word.cmp(p, at, bt))),
            subtraction_carry_reflects_comparison(p, at, bt, False{}),
            carry_order_bit(Word.cmp(p, at, bt), False{}, True{}, False{}))
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          Equal.trans(Bool, S.carry(p, at, Word.not(p, bt), False{}), carry_order(False{}, Word.cmp(p, at, bt)),
            carry_order(True{}, Word.cmp.fin(False{}, True{}, Word.cmp(p, at, bt))),
            subtraction_carry_reflects_comparison(p, at, bt, False{}),
            carry_order_bit(Word.cmp(p, at, bt), False{}, True{}, True{}))
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          Equal.trans(Bool, S.carry(p, at, Word.not(p, bt), True{}), carry_order(True{}, Word.cmp(p, at, bt)),
            carry_order(False{}, Word.cmp.fin(True{}, False{}, Word.cmp(p, at, bt))),
            subtraction_carry_reflects_comparison(p, at, bt, True{}),
            carry_order_bit(Word.cmp(p, at, bt), True{}, False{}, False{}))
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          Equal.trans(Bool, S.carry(p, at, Word.not(p, bt), True{}), carry_order(True{}, Word.cmp(p, at, bt)),
            carry_order(True{}, Word.cmp.fin(True{}, False{}, Word.cmp(p, at, bt))),
            subtraction_carry_reflects_comparison(p, at, bt, True{}),
            carry_order_bit(Word.cmp(p, at, bt), True{}, False{}, True{}))
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          Equal.trans(Bool, S.carry(p, at, Word.not(p, bt), False{}), carry_order(False{}, Word.cmp(p, at, bt)),
            carry_order(False{}, Word.cmp.fin(True{}, True{}, Word.cmp(p, at, bt))),
            subtraction_carry_reflects_comparison(p, at, bt, False{}),
            carry_order_bit(Word.cmp(p, at, bt), True{}, True{}, False{}))
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          Equal.trans(Bool, S.carry(p, at, Word.not(p, bt), True{}), carry_order(True{}, Word.cmp(p, at, bt)),
            carry_order(True{}, Word.cmp.fin(True{}, True{}, Word.cmp(p, at, bt))),
            subtraction_carry_reflects_comparison(p, at, bt, True{}),
            carry_order_bit(Word.cmp(p, at, bt), True{}, True{}, True{}))

law carry_negation_is_strict_order:
  for +order: Cmp
  {Bool.not(carry_order(True{}, order)) == Cmp.is_lt(order) : Bool}
def carry_negation_is_strict_order(order):
  match order:
    case LT{}: {==}
    case EQ{}: {==}
    case GT{}: {==}

law borrow_is_comparison:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Bool.not(S.carry(n, a, Word.not(n, b), True{})) == Cmp.is_lt(Word.cmp(n, a, b)) : Bool}
def borrow_is_comparison(n, a, b):
  Equal.trans(Bool, Bool.not(S.carry(n, a, Word.not(n, b), True{})),
    Bool.not(carry_order(True{}, Word.cmp(n, a, b))), Cmp.is_lt(Word.cmp(n, a, b)),
    Equal.cong(Bool, Bool, Bool.not, S.carry(n, a, Word.not(n, b), True{}), carry_order(True{}, Word.cmp(n, a, b)),
      subtraction_carry_reflects_comparison(n, a, b, True{})), carry_negation_is_strict_order(Word.cmp(n, a, b)))

law subtraction_without_carry_decrements:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Word.adc(n, a, b, True{}, False{}) == N.predecessor(n, Word.sub(n, a, b)) : Word(n)}
def subtraction_without_carry_decrements(n, a, b):
  match n:
    case 0n: {==}
    case 1n+p:
      match a b:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w},
            Word.adc(p, at, bt, True{}, False{}), N.predecessor(p, Word.sub(p, at, bt)),
            subtraction_without_carry_decrements(p, at, bt))
        case WCon{False{}, at} WCon{True{}, bt}: {==}
        case WCon{True{}, at} WCon{False{}, bt}: {==}
        case WCon{True{}, +at} WCon{True{}, +bt}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w},
            Word.adc(p, at, bt, True{}, False{}), N.predecessor(p, Word.sub(p, at, bt)),
            subtraction_without_carry_decrements(p, at, bt))

law high_borrow_exact:
  for +a: Word(32n)
  for +b: Word(32n)
  for +carry: Bool
  {Word.sub(32n, Word.sub(32n, a, b), A.word(Bool.to_u32(Bool.not(carry)))) ==
    Word.adc(32n, a, b, True{}, carry) : Word(32n)}
def high_borrow_exact(a, b, carry):
  match carry:
    case True{}: N.sbb_zero_identity(32n, Word.sub(32n, a, b))
    case False{}:
      Equal.trans(Word(32n), Word.sub(32n, Word.sub(32n, a, b), N.one(31n)),
        N.predecessor(32n, Word.sub(32n, a, b)), Word.adc(32n, a, b, True{}, False{}),
        N.subtract_one_decrements(31n, Word.sub(32n, a, b)),
        Equal.sym(Word(32n), Word.adc(32n, a, b, True{}, False{}), N.predecessor(32n, Word.sub(32n, a, b)), subtraction_without_carry_decrements(32n, a, b)))

law subtraction_blocks:
  for +k: Nat
  for +n: Nat
  for +al: Word(k)
  for +bl: Word(k)
  for +ah: Word(n)
  for +bh: Word(n)
  for +carry: Bool
  {Word.adc(Nat.add(k, n), W.join(k, n, al, ah), W.join(k, n, bl, bh), True{}, carry) ==
    W.join(k, n, Word.adc(k, al, bl, True{}, carry),
      Word.adc(n, ah, bh, True{}, S.carry(k, al, Word.not(k, bl), carry))) : Word(Nat.add(k, n))}
def subtraction_blocks(k, n, al, bl, ah, bh, carry):
  match k:
    case 0n: {==}
    case 1n+p:
      match al bl carry:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), w => WCon{True{}, w},
            Word.adc(Nat.add(p, n), W.join(p, n, at, ah), W.join(p, n, bt, bh), True{}, False{}),
            W.join(p, n, Word.adc(p, at, bt, True{}, False{}), Word.adc(n, ah, bh, True{}, S.carry(p, at, Word.not(p, bt), False{}))),
            subtraction_blocks(p, n, at, bt, ah, bh, False{}))
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), w => WCon{False{}, w},
            Word.adc(Nat.add(p, n), W.join(p, n, at, ah), W.join(p, n, bt, bh), True{}, True{}),
            W.join(p, n, Word.adc(p, at, bt, True{}, True{}), Word.adc(n, ah, bh, True{}, S.carry(p, at, Word.not(p, bt), True{}))),
            subtraction_blocks(p, n, at, bt, ah, bh, True{}))
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), w => WCon{False{}, w},
            Word.adc(Nat.add(p, n), W.join(p, n, at, ah), W.join(p, n, bt, bh), True{}, False{}),
            W.join(p, n, Word.adc(p, at, bt, True{}, False{}), Word.adc(n, ah, bh, True{}, S.carry(p, at, Word.not(p, bt), False{}))),
            subtraction_blocks(p, n, at, bt, ah, bh, False{}))
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), w => WCon{True{}, w},
            Word.adc(Nat.add(p, n), W.join(p, n, at, ah), W.join(p, n, bt, bh), True{}, False{}),
            W.join(p, n, Word.adc(p, at, bt, True{}, False{}), Word.adc(n, ah, bh, True{}, S.carry(p, at, Word.not(p, bt), False{}))),
            subtraction_blocks(p, n, at, bt, ah, bh, False{}))
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), w => WCon{False{}, w},
            Word.adc(Nat.add(p, n), W.join(p, n, at, ah), W.join(p, n, bt, bh), True{}, True{}),
            W.join(p, n, Word.adc(p, at, bt, True{}, True{}), Word.adc(n, ah, bh, True{}, S.carry(p, at, Word.not(p, bt), True{}))),
            subtraction_blocks(p, n, at, bt, ah, bh, True{}))
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), w => WCon{True{}, w},
            Word.adc(Nat.add(p, n), W.join(p, n, at, ah), W.join(p, n, bt, bh), True{}, True{}),
            W.join(p, n, Word.adc(p, at, bt, True{}, True{}), Word.adc(n, ah, bh, True{}, S.carry(p, at, Word.not(p, bt), True{}))),
            subtraction_blocks(p, n, at, bt, ah, bh, True{}))
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), w => WCon{True{}, w},
            Word.adc(Nat.add(p, n), W.join(p, n, at, ah), W.join(p, n, bt, bh), True{}, False{}),
            W.join(p, n, Word.adc(p, at, bt, True{}, False{}), Word.adc(n, ah, bh, True{}, S.carry(p, at, Word.not(p, bt), False{}))),
            subtraction_blocks(p, n, at, bt, ah, bh, False{}))
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), w => WCon{False{}, w},
            Word.adc(Nat.add(p, n), W.join(p, n, at, ah), W.join(p, n, bt, bh), True{}, True{}),
            W.join(p, n, Word.adc(p, at, bt, True{}, True{}), Word.adc(n, ah, bh, True{}, S.carry(p, at, Word.not(p, bt), True{}))),
            subtraction_blocks(p, n, at, bt, ah, bh, True{}))

law bits_sub_borrow:
  for +ah: Word(32n)
  for +al: Word(32n)
  for +bh: Word(32n)
  for +bl: Word(32n)
  for +carry: Bool
  {A.bits(V.Int64{U32.sub(U32.sub(U32{ah}, U32{bh}), Bool.to_u32(Bool.not(carry))), U32.sub(U32{al}, U32{bl})}) ==
    W.join(32n, 32n, Word.sub(32n, al, bl), Word.adc(32n, ah, bh, True{}, carry)) : Word(64n)}
def bits_sub_borrow(ah, al, bh, bl, carry):
  match carry:
    case False{}:
      Equal.cong(Word(32n), Word(64n), w => W.join(32n, 32n, Word.sub(32n, al, bl), w),
        Word.sub(32n, Word.sub(32n, ah, bh), A.word(Bool.to_u32(True{}))), Word.adc(32n, ah, bh, True{}, False{}),
        high_borrow_exact(ah, bh, False{}))
    case True{}:
      Equal.cong(Word(32n), Word(64n), w => W.join(32n, 32n, Word.sub(32n, al, bl), w),
        Word.sub(32n, Word.sub(32n, ah, bh), A.word(Bool.to_u32(False{}))), Word.adc(32n, ah, bh, True{}, True{}),
        high_borrow_exact(ah, bh, True{}))

law wrapping_sub_is_full_word_sub:
  for +a: V.Int64
  for +b: V.Int64
  {A.bits(I.wrapping_sub(a, b)) == Word.sub(64n, A.bits(a), A.bits(b)) : Word(64n)}
def wrapping_sub_is_full_word_sub(a, b):
  match a b:
    case V.Int64{U32{+ah}, U32{+al}} V.Int64{U32{+bh}, U32{+bl}}:
      %borrow_is_comparison(32n, al, bl) :
        {A.bits(V.Int64{U32.sub(U32.sub(U32{ah}, U32{bh}), Bool.to_u32(_)), U32.sub(U32{al}, U32{bl})}) ==
          Word.sub(64n, W.join(32n, 32n, al, ah), W.join(32n, 32n, bl, bh)) : Word(64n)}
      Equal.trans(Word(64n),
        A.bits(V.Int64{U32.sub(U32.sub(U32{ah}, U32{bh}), Bool.to_u32(Bool.not(S.carry(32n, al, Word.not(32n, bl), True{})))), U32.sub(U32{al}, U32{bl})}),
        W.join(32n, 32n, Word.sub(32n, al, bl), Word.adc(32n, ah, bh, True{}, S.carry(32n, al, Word.not(32n, bl), True{}))),
        Word.sub(64n, W.join(32n, 32n, al, ah), W.join(32n, 32n, bl, bh)),
        bits_sub_borrow(ah, al, bh, bl, S.carry(32n, al, Word.not(32n, bl), True{})),
        Equal.sym(Word(64n), Word.sub(64n, W.join(32n, 32n, al, ah), W.join(32n, 32n, bl, bh)),
          W.join(32n, 32n, Word.sub(32n, al, bl), Word.adc(32n, ah, bh, True{}, S.carry(32n, al, Word.not(32n, bl), True{}))),
          subtraction_blocks(32n, 32n, al, bl, ah, bh, True{})))
