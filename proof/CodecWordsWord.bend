# Structural Word algebra for codec inversions, without axioms.
import Base
import ../contract/Logic.bend as L
import ./Foundations.bend as F
import ./Orders.bend as O

def adjust(n: Nat, m: Nat, w: Word(m)) -> Word(n):
  match n m:
    case 0n _:
      WNil{}
    case 1n+p 0n:
      Word.zero(1n+p)
    case 1n+p 1n+q:
      match w:
        case WCon{b, t}:
          WCon{b, adjust(p, q, t)}

def one(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{True{}, Word.zero(p)}

law sum_zero_left:
  for +n: Nat
  for +w: Word(n)
  {Word.add(n, Word.zero(n), w) == w : Word(n)}
def sum_zero_left(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r},
            Word.add(p, Word.zero(p), t), t, sum_zero_left(p, t))
        case WCon{True{}, t}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{True{}, r},
            Word.add(p, Word.zero(p), t), t, sum_zero_left(p, t))

law sum_bit_zero:
  for n: Nat
  for b: Bool
  for x: Word(n)
  for y: Word(n)
  {Word.add(1n+n, WCon{b, x}, WCon{False{}, y}) ==
    WCon{b, Word.add(n, x, y)} : Word(1n+n)}
def sum_bit_zero(n, b, x, y):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

law shift_bit_zero:
  for n: Nat
  for w: Word(n)
  {Word.shl(1n+n, WCon{False{}, w}) == WCon{False{}, Word.shl(n, w)} : Word(1n+n)}
def shift_bit_zero(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          {==}

law multiply_preserves_bit_low:
  for +n: Nat
  for m: Nat
  for a: Word(m)
  for +b: Word(n)
  for +acc: Word(n)
  for +c: Bool
  {Word.mul.go(1n+n, m, a, WCon{False{}, b}, WCon{c, acc}) ==
    WCon{c, Word.mul.go(n, m, a, b, acc)} : Word(1n+n)}
def multiply_preserves_bit_low(n, m, a, b, acc, c):
  match m:
    case 0n:
      {==}
    case 1n+p:
      match a:
        case WCon{False{}, t}:
          %Equal.sym(Word(1n+n), Word.shl(1n+n, WCon{False{}, b}),
            WCon{False{}, Word.shl(n, b)}, shift_bit_zero(n, b)) :
            {Word.mul.go(1n+n, p, t, _, WCon{c, acc}) ==
              WCon{c, Word.mul.go(n, p, t, Word.shl(n, b), acc)} : Word(1n+n)}
          multiply_preserves_bit_low(n, p, t, Word.shl(n, b), acc, c)
        case WCon{True{}, t}:
          %Equal.sym(Word(1n+n), Word.shl(1n+n, WCon{False{}, b}),
            WCon{False{}, Word.shl(n, b)}, shift_bit_zero(n, b)) :
            {Word.mul.go(1n+n, p, t, _, Word.add(1n+n, WCon{c, acc}, WCon{False{}, b})) ==
              WCon{c, Word.mul.go(n, p, t, Word.shl(n, b), Word.add(n, acc, b))} : Word(1n+n)}
          %Equal.sym(Word(1n+n), Word.add(1n+n, WCon{c, acc}, WCon{False{}, b}),
            WCon{c, Word.add(n, acc, b)}, sum_bit_zero(n, c, acc, b)) :
            {Word.mul.go(1n+n, p, t, WCon{False{}, Word.shl(n, b)}, _) ==
              WCon{c, Word.mul.go(n, p, t, Word.shl(n, b), Word.add(n, acc, b))} : Word(1n+n)}
          multiply_preserves_bit_low(n, p, t, Word.shl(n, b), Word.add(n, acc, b), c)

law multiply_width_zero:
  for m: Nat
  for w: Word(m)
  {Word.mul.go(0n, m, w, WNil{}, WNil{}) == WNil{} : Word(0n)}
def multiply_width_zero(m, w):
  match m:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          multiply_width_zero(p, t)
        case WCon{True{}, t}:
          multiply_width_zero(p, t)

law shift_zero:
  for +n: Nat
  {Word.shl.put(n, False{}, Word.zero(n)) == Word.zero(n) : Word(n)}
def shift_zero(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r},
        Word.shl.put(p, False{}, Word.zero(p)), Word.zero(p), shift_zero(p))

law shift_one:
  for n: Nat
  {Word.shl(1n+n, one(1n+n)) == WCon{False{}, one(n)} : Word(1n+n)}
def shift_one(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Word(p), Word(2n+p), r => WCon{False{}, WCon{True{}, r}},
        Word.shl.put(p, False{}, Word.zero(p)), Word.zero(p), shift_zero(p))

law multiply_one_adjusts:
  for +n: Nat
  for +m: Nat
  for +w: Word(m)
  {Word.mul.go(n, m, w, one(n), Word.zero(n)) == adjust(n, m, w) : Word(n)}
def multiply_one_adjusts(n, m, w):
  match n m:
    case 0n _:
      multiply_width_zero(m, w)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      match w:
        case WCon{False{}, t}:
          %Equal.sym(Word(1n+p), Word.shl(1n+p, one(1n+p)),
            WCon{False{}, one(p)}, shift_one(p)) :
            {Word.mul.go(1n+p, q, t, _, Word.zero(1n+p)) == WCon{False{}, adjust(p, q, t)} : Word(1n+p)}
          Equal.trans(Word(1n+p),
            Word.mul.go(1n+p, q, t, WCon{False{}, one(p)}, WCon{False{}, Word.zero(p)}),
            WCon{False{}, Word.mul.go(p, q, t, one(p), Word.zero(p))}, WCon{False{}, adjust(p, q, t)},
            multiply_preserves_bit_low(p, q, t, one(p), Word.zero(p), False{}),
            Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r},
              Word.mul.go(p, q, t, one(p), Word.zero(p)), adjust(p, q, t), multiply_one_adjusts(p, q, t)))

        case WCon{True{}, t}:
          %Equal.sym(Word(1n+p), Word.add(1n+p, Word.zero(1n+p), one(1n+p)),
            one(1n+p), sum_zero_left(1n+p, one(1n+p))) :
            {Word.mul.go(1n+p, q, t, Word.shl(1n+p, one(1n+p)), _) == WCon{True{}, adjust(p, q, t)} : Word(1n+p)}
          %Equal.sym(Word(1n+p), Word.shl(1n+p, one(1n+p)),
            WCon{False{}, one(p)}, shift_one(p)) :
            {Word.mul.go(1n+p, q, t, _, one(1n+p)) == WCon{True{}, adjust(p, q, t)} : Word(1n+p)}
          Equal.trans(Word(1n+p),
            Word.mul.go(1n+p, q, t, WCon{False{}, one(p)}, WCon{True{}, Word.zero(p)}),
            WCon{True{}, Word.mul.go(p, q, t, one(p), Word.zero(p))}, WCon{True{}, adjust(p, q, t)},
            multiply_preserves_bit_low(p, q, t, one(p), Word.zero(p), True{}),
            Equal.cong(Word(p), Word(1n+p), r => WCon{True{}, r},
              Word.mul.go(p, q, t, one(p), Word.zero(p)), adjust(p, q, t), multiply_one_adjusts(p, q, t)))

# The first k bits are least significant.
def zeros_low(k: Nat, -n: Nat, w: Word(n)) -> Word(Nat.add(k, n)):
  match k:
    case 0n:
      w
    case 1n+p:
      WCon{False{}, zeros_low(p, n, w)}

law multiply_power_two:
  for +k: Nat
  for +n: Nat
  for +m: Nat
  for +w: Word(m)
  {Word.mul.go(Nat.add(k, n), m, w, zeros_low(k, n, one(n)), Word.zero(Nat.add(k, n))) ==
    zeros_low(k, n, adjust(n, m, w)) : Word(Nat.add(k, n))}
def multiply_power_two(k, n, m, w):
  match k:
    case 0n:
      multiply_one_adjusts(n, m, w)
    case 1n+p:
      Equal.trans(Word(1n+Nat.add(p, n)),
        Word.mul.go(1n+Nat.add(p, n), m, w, WCon{False{}, zeros_low(p, n, one(n))}, WCon{False{}, Word.zero(Nat.add(p, n))}),
        WCon{False{}, Word.mul.go(Nat.add(p, n), m, w, zeros_low(p, n, one(n)), Word.zero(Nat.add(p, n)))},
        WCon{False{}, zeros_low(p, n, adjust(n, m, w))},
        multiply_preserves_bit_low(Nat.add(p, n), m, w, zeros_low(p, n, one(n)), Word.zero(Nat.add(p, n)), False{}),
        Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), r => WCon{False{}, r},
          Word.mul.go(Nat.add(p, n), m, w, zeros_low(p, n, one(n)), Word.zero(Nat.add(p, n))),
          zeros_low(p, n, adjust(n, m, w)), multiply_power_two(p, n, m, w)))

# Binary concatenation: lo occupies the k least significant bits.
def join(k: Nat, -n: Nat, lo: Word(k), hi: Word(n)) -> Word(Nat.add(k, n)):
  match k:
    case 0n:
      hi
    case 1n+p:
      match lo:
        case WCon{b, t}:
          WCon{b, join(p, n, t, hi)}

def ones(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{True{}, ones(p)}

law sum_zero_right:
  for +n: Nat
  for +w: Word(n)
  {Word.add(n, w, Word.zero(n)) == w : Word(n)}
def sum_zero_right(n, w):
  Equal.trans(Word(n), Word.add(n, w, Word.zero(n)), Word.add(n, Word.zero(n), w), w,
    Word.add_comm(n, w, Word.zero(n)), sum_zero_left(n, w))

law sum_blocks_separate:
  for +k: Nat
  for +n: Nat
  for +lo: Word(k)
  for +hi: Word(n)
  {Word.add(Nat.add(k, n), zeros_low(k, n, hi), join(k, n, lo, Word.zero(n))) ==
    join(k, n, lo, hi) : Word(Nat.add(k, n))}
def sum_blocks_separate(k, n, lo, hi):
  match k:
    case 0n:
      sum_zero_right(n, hi)
    case 1n+p:
      match lo:
        case WCon{False{}, t}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), r => WCon{False{}, r},
            Word.add(Nat.add(p, n), zeros_low(p, n, hi), join(p, n, t, Word.zero(n))),
            join(p, n, t, hi), sum_blocks_separate(p, n, t, hi))
        case WCon{True{}, t}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), r => WCon{True{}, r},
            Word.add(Nat.add(p, n), zeros_low(p, n, hi), join(p, n, t, Word.zero(n))),
            join(p, n, t, hi), sum_blocks_separate(p, n, t, hi))

law mask_zero:
  for +n: Nat
  for +w: Word(n)
  {Word.and(n, w, Word.zero(n)) == Word.zero(n) : Word(n)}
def mask_zero(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r},
            Word.and(p, t, Word.zero(p)), Word.zero(p), mask_zero(p, t))
        case WCon{True{}, t}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r},
            Word.and(p, t, Word.zero(p)), Word.zero(p), mask_zero(p, t))

law mask_low:
  for +k: Nat
  for +n: Nat
  for +w: Word(Nat.add(k, n))
  {Word.and(Nat.add(k, n), w, join(k, n, ones(k), Word.zero(n))) ==
    join(k, n, adjust(k, Nat.add(k, n), w), Word.zero(n)) : Word(Nat.add(k, n))}
def mask_low(k, n, w):
  match k:
    case 0n:
      mask_zero(n, w)
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), r => WCon{False{}, r},
            Word.and(Nat.add(p, n), t, join(p, n, ones(p), Word.zero(n))),
            join(p, n, adjust(p, Nat.add(p, n), t), Word.zero(n)), mask_low(p, n, t))
        case WCon{True{}, t}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), r => WCon{True{}, r},
            Word.and(Nat.add(p, n), t, join(p, n, ones(p), Word.zero(n))),
            join(p, n, adjust(p, Nat.add(p, n), t), Word.zero(n)), mask_low(p, n, t))

# A lexicographic comparison cannot hide a larger tail.

law limit_of_tail:
  for a: Bool
  for b: Bool
  for c: Cmp
  for e: {Cmp.is_le(Word.cmp.fin(a, b, c)) == True{} : Bool}
  {Cmp.is_le(c) == True{} : Bool}
def limit_of_tail(a, b, c, e):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      e

law word_until_zero:
  for +n: Nat
  for +w: Word(n)
  for +e: {Cmp.is_le(Word.cmp(n, w, Word.zero(n))) == True{} : Bool}
  {w == Word.zero(n) : Word(n)}
def word_until_zero(n, w, e):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r}, t, Word.zero(p),
            word_until_zero(p, t, limit_of_tail(False{}, False{}, Word.cmp(p, t, Word.zero(p)), e)))
        case WCon{True{}, t}:
          tail = word_until_zero(p, t, limit_of_tail(True{}, False{}, Word.cmp(p, t, Word.zero(p)), e))
          order = Equal.trans(Cmp, Word.cmp(p, t, Word.zero(p)), Word.cmp(p, Word.zero(p), Word.zero(p)), EQ{},
            Equal.cong(Word(p), Cmp, r => Word.cmp(p, r, Word.zero(p)), t, Word.zero(p), tail), O.word_refl(p, Word.zero(p)))
          F.absurd_boolean({WCon{True{}, t} == Word.zero(1n+p) : Word(1n+p)},
            Equal.trans(Bool, False{}, Cmp.is_le(Word.cmp.fin(True{}, False{}, Word.cmp(p, t, Word.zero(p)))), True{},
              Equal.sym(Bool, Cmp.is_le(Word.cmp.fin(True{}, False{}, Word.cmp(p, t, Word.zero(p)))), False{},
                Equal.cong(Cmp, Bool, c => Cmp.is_le(Word.cmp.fin(True{}, False{}, c)), Word.cmp(p, t, Word.zero(p)), EQ{}, order)), e))

law limit_bits_low:
  for +k: Nat
  for +n: Nat
  for +w: Word(Nat.add(k, n))
  for e: {Cmp.is_le(Word.cmp(Nat.add(k, n), w, join(k, n, ones(k), Word.zero(n)))) == True{} : Bool}
  {w == join(k, n, adjust(k, Nat.add(k, n), w), Word.zero(n)) : Word(Nat.add(k, n))}
def limit_bits_low(k, n, w, e):
  match k:
    case 0n:
      word_until_zero(n, w, e)
    case 1n+p:
      match w:
        case WCon{b, t}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), r => WCon{b, r},
            t, join(p, n, adjust(p, Nat.add(p, n), t), Word.zero(n)),
            limit_bits_low(p, n, t, limit_of_tail(b, True{}, Word.cmp(Nat.add(p, n), t, join(p, n, ones(p), Word.zero(n))), e)))
