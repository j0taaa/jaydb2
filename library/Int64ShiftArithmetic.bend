# Independent natural interpretation of every bit shift, including lost top bit.
import Base
import ./Int64Shifts.bend as W
import ./Value.bend as V
import ./Int64.bend as I
import ./Int64Proofs.bend as A
import ../proof/CodecSumsBits.bend as S

law double_is_self_sum:
  for +n: Nat
  {Nat.double(n) == Nat.add(n, n) : Nat}
def double_is_self_sum(n):
  match n:
    case 0n: {==}
    case 1n+p:
      Equal.trans(Nat, 2n+Nat.double(p), 2n+Nat.add(p, p), 1n+Nat.add(p, 1n+p),
        Equal.cong(Nat, Nat, n => 2n+n, Nat.double(p), Nat.add(p, p), double_is_self_sum(p)),
        Equal.cong(Nat, Nat, n => 1n+n, 1n+Nat.add(p, p), Nat.add(p, 1n+p),
          Equal.sym(Nat, Nat.add(p, 1n+p), 1n+Nat.add(p, p), A.add_right_successor(p, p))))

law double_adder_is_shift:
  for +n: Nat
  for +w: Word(n)
  for +carry: Bool
  {Word.adc(n, w, w, False{}, carry) == Word.shl.put(n, carry, w) : Word(n)}
def double_adder_is_shift(n, w, carry):
  match n:
    case 0n: {==}
    case 1n+p:
      match w carry:
        case WCon{False{}, +tail} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            Word.adc(p, tail, tail, False{}, False{}), Word.shl.put(p, False{}, tail), double_adder_is_shift(p, tail, False{}))
        case WCon{False{}, +tail} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w},
            Word.adc(p, tail, tail, False{}, False{}), Word.shl.put(p, False{}, tail), double_adder_is_shift(p, tail, False{}))
        case WCon{True{}, +tail} False{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w},
            Word.adc(p, tail, tail, False{}, True{}), Word.shl.put(p, True{}, tail), double_adder_is_shift(p, tail, True{}))
        case WCon{True{}, +tail} True{}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{True{}, w},
            Word.adc(p, tail, tail, False{}, True{}), Word.shl.put(p, True{}, tail), double_adder_is_shift(p, tail, True{}))

law double_carry_is_end:
  for +n: Nat
  for +w: Word(n)
  for +carry: Bool
  {S.carry(n, w, w, carry) == W.end_bit(n, carry, w) : Bool}
def double_carry_is_end(n, w, carry):
  match n:
    case 0n: {==}
    case 1n+p:
      match w carry:
        case WCon{False{}, +tail} False{}: double_carry_is_end(p, tail, False{})
        case WCon{False{}, +tail} True{}: double_carry_is_end(p, tail, False{})
        case WCon{True{}, +tail} False{}: double_carry_is_end(p, tail, True{})
        case WCon{True{}, +tail} True{}: double_carry_is_end(p, tail, True{})

law end_zero_is_top:
  for +n: Nat
  for +w: Word(n)
  {W.end_bit(n, False{}, w) == A.top(n, w) : Bool}
def end_zero_is_top(n, w):
  match n:
    case 0n: {==}
    case 1n+p: W.end_bit_is_top(p, False{}, w)

law doubled_word_is_shifted:
  for +n: Nat
  for +w: Word(n)
  {Word.add(n, w, w) == Word.shl(n, w) : Word(n)}
def doubled_word_is_shifted(n, w):
  Equal.trans(Word(n), Word.add(n, w, w), Word.shl.put(n, False{}, w), Word.shl(n, w),
    double_adder_is_shift(n, w, False{}), Equal.sym(Word(n), Word.shl(n, w), Word.shl.put(n, False{}, w), W.shift_is_put_zero(n, w)))

law double_carry_is_top:
  for +n: Nat
  for +w: Word(n)
  {S.carry(n, w, w, False{}) == A.top(n, w) : Bool}
def double_carry_is_top(n, w):
  Equal.trans(Bool, S.carry(n, w, w, False{}), W.end_bit(n, False{}, w), A.top(n, w),
    double_carry_is_end(n, w, False{}), end_zero_is_top(n, w))

law shift_word_natural:
  for +n: Nat
  for +w: Word(n)
  {Nat.double(Word.to_nat(n, w)) == Nat.add(Word.to_nat(n, Word.shl(n, w)), A.spill(n, A.top(n, w))) : Nat}
def shift_word_natural(n, w):
  Equal.trans(Nat, Nat.double(Word.to_nat(n, w)), Nat.add(Word.to_nat(n, w), Nat.add(Word.to_nat(n, w), 0n)),
    Nat.add(Word.to_nat(n, Word.shl(n, w)), A.spill(n, A.top(n, w))),
    Equal.trans(Nat, Nat.double(Word.to_nat(n, w)), Nat.add(Word.to_nat(n, w), Word.to_nat(n, w)),
      Nat.add(Word.to_nat(n, w), Nat.add(Word.to_nat(n, w), 0n)), double_is_self_sum(Word.to_nat(n, w)),
      Equal.cong(Nat, Nat, p => Nat.add(Word.to_nat(n, w), p), Word.to_nat(n, w), Nat.add(Word.to_nat(n, w), 0n),
        Equal.sym(Nat, Nat.add(Word.to_nat(n, w), 0n), Word.to_nat(n, w), A.add_zero_right(Word.to_nat(n, w))))),
    Equal.trans(Nat, Nat.add(Word.to_nat(n, w), Nat.add(Word.to_nat(n, w), 0n)),
      Nat.add(Word.to_nat(n, Word.add(n, w, w)), A.spill(n, S.carry(n, w, w, False{}))),
      Nat.add(Word.to_nat(n, Word.shl(n, w)), A.spill(n, A.top(n, w))), A.adc_natural(n, w, w, False{}),
      Equal.trans(Nat, Nat.add(Word.to_nat(n, Word.add(n, w, w)), A.spill(n, S.carry(n, w, w, False{}))),
        Nat.add(Word.to_nat(n, Word.shl(n, w)), A.spill(n, S.carry(n, w, w, False{}))),
        Nat.add(Word.to_nat(n, Word.shl(n, w)), A.spill(n, A.top(n, w))),
        Equal.cong(Word(n), Nat, p => Nat.add(Word.to_nat(n, p), A.spill(n, S.carry(n, w, w, False{}))),
          Word.add(n, w, w), Word.shl(n, w), doubled_word_is_shifted(n, w)),
        Equal.cong(Bool, Nat, c => Nat.add(Word.to_nat(n, Word.shl(n, w)), A.spill(n, c)),
          S.carry(n, w, w, False{}), A.top(n, w), double_carry_is_top(n, w)))))

law padded_word_measure:
  for +n: Nat
  for +w: Word(n)
  {Word.to_nat(1n+n, Word.shr.pad(n, w)) == Word.to_nat(n, w) : Nat}
def padded_word_measure(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}: {==}
    case 1n+p:
      match w:
        case WCon{False{}, +tail}:
          Equal.cong(Nat, Nat, Nat.double, Word.to_nat(1n+p, Word.shr.pad(p, tail)), Word.to_nat(p, tail), padded_word_measure(p, tail))
        case WCon{True{}, +tail}:
          Equal.cong(Nat, Nat, n => 1n+Nat.double(n), Word.to_nat(1n+p, Word.shr.pad(p, tail)), Word.to_nat(p, tail), padded_word_measure(p, tail))

law right_shift_word_natural:
  for +n: Nat
  for +w: Word(1n+n)
  {Word.to_nat(1n+n, w) == A.place(W.head_bit(1n+n, w), Word.to_nat(1n+n, Word.shr(1n+n, w))) : Nat}
def right_shift_word_natural(n, w):
  match w:
    case WCon{False{}, +tail}:
      Equal.cong(Nat, Nat, Nat.double, Word.to_nat(n, tail), Word.to_nat(1n+n, Word.shr.pad(n, tail)),
        Equal.sym(Nat, Word.to_nat(1n+n, Word.shr.pad(n, tail)), Word.to_nat(n, tail), padded_word_measure(n, tail)))
    case WCon{True{}, +tail}:
      Equal.cong(Nat, Nat, n => 1n+Nat.double(n), Word.to_nat(n, tail), Word.to_nat(1n+n, Word.shr.pad(n, tail)),
        Equal.sym(Nat, Word.to_nat(1n+n, Word.shr.pad(n, tail)), Word.to_nat(n, tail), padded_word_measure(n, tail)))

law actual_left_shift_natural:
  for +x: V.Int64
  {Nat.double(A.unsigned(x)) == Nat.add(A.unsigned(I.shl(x)), A.spill(64n, I.negative(x))) : Nat}
def actual_left_shift_natural(x):
  Equal.trans(Nat, Nat.double(A.unsigned(x)), Nat.add(Word.to_nat(64n, Word.shl(64n, A.bits(x))), A.spill(64n, A.top(64n, A.bits(x)))),
    Nat.add(A.unsigned(I.shl(x)), A.spill(64n, I.negative(x))), shift_word_natural(64n, A.bits(x)),
    Equal.trans(Nat, Nat.add(Word.to_nat(64n, Word.shl(64n, A.bits(x))), A.spill(64n, A.top(64n, A.bits(x)))),
      Nat.add(A.unsigned(I.shl(x)), A.spill(64n, A.top(64n, A.bits(x)))), Nat.add(A.unsigned(I.shl(x)), A.spill(64n, I.negative(x))),
      Equal.cong(Word(64n), Nat, w => Nat.add(Word.to_nat(64n, w), A.spill(64n, A.top(64n, A.bits(x)))),
        Word.shl(64n, A.bits(x)), A.bits(I.shl(x)), Equal.sym(Word(64n), A.bits(I.shl(x)), Word.shl(64n, A.bits(x)), W.shl_is_full_word_shift(x))),
      Equal.cong(Bool, Nat, c => Nat.add(A.unsigned(I.shl(x)), A.spill(64n, c)), A.top(64n, A.bits(x)), I.negative(x),
        Equal.sym(Bool, I.negative(x), A.top(64n, A.bits(x)), A.negative_is_sign_bit(x)))))
