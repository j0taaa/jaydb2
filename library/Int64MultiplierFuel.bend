# Fuel adequacy is proved from finite word structure and the actual right shift.
import Base
import ./Int64Shifts.bend as W
import ./Value.bend as V
import ./Int64.bend as I
import ./Int64Proofs.bend as A

def shift_many(steps: Nat, +width: Nat, word: Word(width)) -> Word(width):
  match steps:
    case 0n: word
    case 1n+p: shift_many(p, width, Word.shr(width, word))

law shift_padding_commutes:
  for +n: Nat
  for +word: Word(n)
  {Word.shr(1n+n, Word.shr.pad(n, word)) == Word.shr.pad(n, Word.shr(n, word)) : Word(1n+n)}
def shift_padding_commutes(n, word):
  match n:
    case 0n:
      match word:
        case WNil{}: {==}
    case 1n+p:
      match word:
        case WCon{b, tail}: {==}

law many_shifts_commute_with_padding:
  for +steps: Nat
  for +n: Nat
  for +word: Word(n)
  {shift_many(steps, 1n+n, Word.shr.pad(n, word)) == Word.shr.pad(n, shift_many(steps, n, word)) : Word(1n+n)}
def many_shifts_commute_with_padding(steps, n, word):
  match steps:
    case 0n: {==}
    case 1n+p:
      %Equal.sym(Word(1n+n), Word.shr(1n+n, Word.shr.pad(n, word)), Word.shr.pad(n, Word.shr(n, word)), shift_padding_commutes(n, word)) :
        {shift_many(p, 1n+n, _) == Word.shr.pad(n, shift_many(1n+p, n, word)) : Word(1n+n)}
      many_shifts_commute_with_padding(p, n, Word.shr(n, word))

law padded_zero_is_zero:
  for +n: Nat
  {Word.shr.pad(n, Word.zero(n)) == Word.zero(1n+n) : Word(1n+n)}
def padded_zero_is_zero(n):
  match n:
    case 0n: {==}
    case 1n+p:
      Equal.cong(Word(1n+p), Word(2n+p), w => WCon{False{}, w}, Word.shr.pad(p, Word.zero(p)), Word.zero(1n+p), padded_zero_is_zero(p))

law width_shifts_exhaust_every_word:
  for +n: Nat
  for +word: Word(n)
  {shift_many(n, n, word) == Word.zero(n) : Word(n)}
def width_shifts_exhaust_every_word(n, word):
  match n:
    case 0n:
      match word:
        case WNil{}: {==}
    case 1n+p:
      match word:
        case WCon{b, +tail}:
          Equal.trans(Word(1n+p), shift_many(p, 1n+p, Word.shr.pad(p, tail)),
            Word.shr.pad(p, shift_many(p, p, tail)), Word.zero(1n+p), many_shifts_commute_with_padding(p, p, tail),
            Equal.trans(Word(1n+p), Word.shr.pad(p, shift_many(p, p, tail)), Word.shr.pad(p, Word.zero(p)), Word.zero(1n+p),
              Equal.cong(Word(p), Word(1n+p), w => Word.shr.pad(p, w), shift_many(p, p, tail), Word.zero(p), width_shifts_exhaust_every_word(p, tail)), padded_zero_is_zero(p)))

def shrink(steps: Nat, number: V.Int64) -> V.Int64:
  match steps:
    case 0n: number
    case 1n+p: shrink(p, I.shr(number))

law shrinking_is_actual_word_shifting:
  for +steps: Nat
  for +number: V.Int64
  {A.bits(shrink(steps, number)) == shift_many(steps, 64n, A.bits(number)) : Word(64n)}
def shrinking_is_actual_word_shifting(steps, number):
  match steps:
    case 0n: {==}
    case 1n+p:
      Equal.trans(Word(64n), A.bits(shrink(p, I.shr(number))), shift_many(p, 64n, A.bits(I.shr(number))), shift_many(1n+p, 64n, A.bits(number)),
        shrinking_is_actual_word_shifting(p, I.shr(number)),
        Equal.cong(Word(64n), Word(64n), w => shift_many(p, 64n, w), A.bits(I.shr(number)), Word.shr(64n, A.bits(number)), W.shr_is_full_word_shift(number)))

law sixty_four_steps_cover_every_multiplier:
  for +number: V.Int64
  {shrink(64n, number) == V.Int64{0, 0} : V.Int64}
def sixty_four_steps_cover_every_multiplier(number):
  A.bits_injective(shrink(64n, number), V.Int64{0, 0},
    Equal.trans(Word(64n), A.bits(shrink(64n, number)), shift_many(64n, 64n, A.bits(number)), Word.zero(64n),
      shrinking_is_actual_word_shifting(64n, number), width_shifts_exhaust_every_word(64n, A.bits(number))))
