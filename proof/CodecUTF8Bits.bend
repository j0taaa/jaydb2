# General bitwise arithmetic for reconstructing UTF-8 payloads.
import Base
import ../contract/Bytes.bend as B
import ../src/Codec.bend as C
import ./CodecWordsWord.bend as W
import ./Orders.bend as O

# Subtraction uses the complement of addition's initial carry.
law adc_sbb_cancel:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +carry: Bool
  {Word.adc(n, Word.adc(n, a, b, False{}, carry), b, True{}, Bool.not(carry)) == a : Word(n)}
def adc_sbb_cancel(n, a, b, carry):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b carry:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r},
            Word.adc(p, Word.adc(p, at, bt, False{}, False{}), bt, True{}, True{}), at,
            adc_sbb_cancel(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r},
            Word.adc(p, Word.adc(p, at, bt, False{}, False{}), bt, True{}, True{}), at,
            adc_sbb_cancel(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r},
            Word.adc(p, Word.adc(p, at, bt, False{}, False{}), bt, True{}, True{}), at,
            adc_sbb_cancel(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r},
            Word.adc(p, Word.adc(p, at, bt, False{}, True{}), bt, True{}, False{}), at,
            adc_sbb_cancel(p, at, bt, True{}))
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{True{}, r},
            Word.adc(p, Word.adc(p, at, bt, False{}, False{}), bt, True{}, True{}), at,
            adc_sbb_cancel(p, at, bt, False{}))
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{True{}, r},
            Word.adc(p, Word.adc(p, at, bt, False{}, True{}), bt, True{}, False{}), at,
            adc_sbb_cancel(p, at, bt, True{}))
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{True{}, r},
            Word.adc(p, Word.adc(p, at, bt, False{}, True{}), bt, True{}, False{}), at,
            adc_sbb_cancel(p, at, bt, True{}))
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{True{}, r},
            Word.adc(p, Word.adc(p, at, bt, False{}, True{}), bt, True{}, False{}), at,
            adc_sbb_cancel(p, at, bt, True{}))

law sum_subtract_cancels:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Word.sub(n, Word.add(n, a, b), b) == a : Word(n)}
def sum_subtract_cancels(n, a, b):
  adc_sbb_cancel(n, a, b, False{})

law sum_blocks:
  for +k: Nat
  for +n: Nat
  for +lo: Word(k)
  for +hi: Word(n)
  for +other: Word(n)
  {Word.add(Nat.add(k, n), W.zeros_low(k, n, hi), W.join(k, n, lo, other)) ==
    W.join(k, n, lo, Word.add(n, hi, other)) : Word(Nat.add(k, n))}
def sum_blocks(k, n, lo, hi, other):
  match k:
    case 0n:
      {==}
    case 1n+p:
      match lo:
        case WCon{False{}, +t}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), r => WCon{False{}, r},
            Word.add(Nat.add(p, n), W.zeros_low(p, n, hi), W.join(p, n, t, other)), W.join(p, n, t, Word.add(n, hi, other)),
            sum_blocks(p, n, t, hi, other))
        case WCon{True{}, +t}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), r => WCon{True{}, r},
            Word.add(Nat.add(p, n), W.zeros_low(p, n, hi), W.join(p, n, t, other)), W.join(p, n, t, Word.add(n, hi, other)),
            sum_blocks(p, n, t, hi, other))

law subtract_blocks:
  for +k: Nat
  for +n: Nat
  for +lo: Word(k)
  for +hi: Word(n)
  for +other: Word(n)
  {Word.sub(Nat.add(k, n), W.join(k, n, lo, hi), W.zeros_low(k, n, other)) ==
    W.join(k, n, lo, Word.sub(n, hi, other)) : Word(Nat.add(k, n))}
def subtract_blocks(k, n, lo, hi, other):
  match k:
    case 0n:
      {==}
    case 1n+p:
      match lo:
        case WCon{False{}, +t}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), r => WCon{False{}, r},
            Word.sub(Nat.add(p, n), W.join(p, n, t, hi), W.zeros_low(p, n, other)), W.join(p, n, t, Word.sub(n, hi, other)),
            subtract_blocks(p, n, t, hi, other))
        case WCon{True{}, +t}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), r => WCon{True{}, r},
            Word.sub(Nat.add(p, n), W.join(p, n, t, hi), W.zeros_low(p, n, other)), W.join(p, n, t, Word.sub(n, hi, other)),
            subtract_blocks(p, n, t, hi, other))

def bits(x: U32) -> Word(32n):
  U32{w} = x
  w

def continuation(lo: Word(6n)) -> U32:
  U32{W.join(6n, 26n, lo, W.adjust(26n, 32n, bits(2)))}

law resume_reconstructs_six_bits_exact:
  for +cp: U32
  for +lo: Word(6n)
  {(cp * 64 + continuation(lo) - 128 : U32) ==
    U32{W.join(6n, 26n, lo, W.adjust(26n, 32n, bits(cp)))} : U32}
def resume_reconstructs_six_bits_exact(cp, lo):
  match cp:
    case U32{+w}:
      %Equal.sym(Word(32n), Word.mul(32n, w, bits(64)),
        W.zeros_low(6n, 26n, W.adjust(26n, 32n, w)), W.multiply_power_two(6n, 26n, 32n, w)) :
        {U32{Word.sub(32n, Word.add(32n, _, bits(continuation(lo))), bits(128))} == U32{W.join(6n, 26n, lo, W.adjust(26n, 32n, w))} : U32}
      %Equal.sym(Word(32n), Word.add(32n, W.zeros_low(6n, 26n, W.adjust(26n, 32n, w)), bits(continuation(lo))),
        W.join(6n, 26n, lo, Word.add(26n, W.adjust(26n, 32n, w), W.adjust(26n, 32n, bits(2)))),
        sum_blocks(6n, 26n, lo, W.adjust(26n, 32n, w), W.adjust(26n, 32n, bits(2)))) :
        {U32{Word.sub(32n, _, bits(128))} == U32{W.join(6n, 26n, lo, W.adjust(26n, 32n, w))} : U32}
      %Equal.sym(Word(32n), Word.sub(32n, W.join(6n, 26n, lo, Word.add(26n, W.adjust(26n, 32n, w), W.adjust(26n, 32n, bits(2)))), bits(128)),
        W.join(6n, 26n, lo, Word.sub(26n, Word.add(26n, W.adjust(26n, 32n, w), W.adjust(26n, 32n, bits(2))), W.adjust(26n, 32n, bits(2)))),
        subtract_blocks(6n, 26n, lo, Word.add(26n, W.adjust(26n, 32n, w), W.adjust(26n, 32n, bits(2))), W.adjust(26n, 32n, bits(2)))) :
        {U32{_} == U32{W.join(6n, 26n, lo, W.adjust(26n, 32n, w))} : U32}
      Equal.cong(Word(26n), U32, z => U32{W.join(6n, 26n, lo, z)},
        Word.sub(26n, Word.add(26n, W.adjust(26n, 32n, w), W.adjust(26n, 32n, bits(2))), W.adjust(26n, 32n, bits(2))),
        W.adjust(26n, 32n, w), sum_subtract_cancels(26n, W.adjust(26n, 32n, w), W.adjust(26n, 32n, bits(2))))

law mask_six_bits:
  for +cp: U32
  {U32.and(cp, 63) == U32{W.join(6n, 26n, W.adjust(6n, 32n, bits(cp)), Word.zero(26n))} : U32}
def mask_six_bits(cp):
  match cp:
    case U32{w}:
      Equal.cong(Word(32n), U32, z => U32{z}, Word.and(32n, w, W.join(6n, 26n, W.ones(6n), Word.zero(26n))),
        W.join(6n, 26n, W.adjust(6n, 32n, w), Word.zero(26n)), W.mask_low(6n, 26n, w))

def scalar2(hi: Word(5n), b0: Word(6n)) -> U32:
  U32{W.join(6n, 26n, b0, W.join(5n, 21n, hi, Word.zero(21n)))}

law utf8_form_2_bytes:
  for +hi: Word(5n)
  for +b0: Word(6n)
  {B.utf8_code_emit(scalar2(hi, b0), False{}, True{}, False{}) == [U32{W.join(5n, 27n, hi, W.adjust(27n, 32n, bits(6)))}, continuation(b0)] : List<&2, U32>}
def utf8_form_2_bytes(hi, b0):
  match hi b0:
    case WCon{+hi0, WCon{+hi1, WCon{+hi2, WCon{+hi3, WCon{+hi4, WNil{}}}}}} WCon{+b00, WCon{+b01, WCon{+b02, WCon{+b03, WCon{+b04, WCon{+b05, WNil{}}}}}}}:
      %Equal.sym(U32, U32.and(scalar2(hi, b0), 63), U32{W.join(6n, 26n, W.adjust(6n, 32n, bits(scalar2(hi, b0))), Word.zero(26n))}, mask_six_bits(scalar2(hi, b0))) :
        {[U32.or(192, U32.shrn(scalar2(hi, b0), 6n)), U32.or(128, _)] == [U32{W.join(5n, 27n, hi, W.adjust(27n, 32n, bits(6)))}, continuation(b0)] : List<&2, U32>}
      {==}

def scalar3(hi: Word(4n), b0: Word(6n), b1: Word(6n)) -> U32:
  U32{W.join(6n, 26n, b1, W.join(6n, 20n, b0, W.join(4n, 16n, hi, Word.zero(16n))))}

law utf8_form_3_bytes:
  for +hi: Word(4n)
  for +b0: Word(6n)
  for +b1: Word(6n)
  {B.utf8_code_emit(scalar3(hi, b0, b1), False{}, False{}, True{}) == [U32{W.join(4n, 28n, hi, W.adjust(28n, 32n, bits(14)))}, continuation(b0), continuation(b1)] : List<&2, U32>}
def utf8_form_3_bytes(hi, b0, b1):
  match hi b0 b1:
    case WCon{+hi0, WCon{+hi1, WCon{+hi2, WCon{+hi3, WNil{}}}}} WCon{+b00, WCon{+b01, WCon{+b02, WCon{+b03, WCon{+b04, WCon{+b05, WNil{}}}}}}} WCon{+b10, WCon{+b11, WCon{+b12, WCon{+b13, WCon{+b14, WCon{+b15, WNil{}}}}}}}:
      %Equal.sym(U32, U32.and(U32.shrn(scalar3(hi, b0, b1), 6n), 63), U32{W.join(6n, 26n, W.adjust(6n, 32n, bits(U32.shrn(scalar3(hi, b0, b1), 6n))), Word.zero(26n))}, mask_six_bits(U32.shrn(scalar3(hi, b0, b1), 6n))) :
        {[U32.or(224, U32.shrn(scalar3(hi, b0, b1), 12n)), U32.or(128, _), U32.or(128, U32.and(scalar3(hi, b0, b1), 63))] == [U32{W.join(4n, 28n, hi, W.adjust(28n, 32n, bits(14)))}, continuation(b0), continuation(b1)] : List<&2, U32>}
      %Equal.sym(U32, U32.and(scalar3(hi, b0, b1), 63), U32{W.join(6n, 26n, W.adjust(6n, 32n, bits(scalar3(hi, b0, b1))), Word.zero(26n))}, mask_six_bits(scalar3(hi, b0, b1))) :
        {[U32.or(224, U32.shrn(scalar3(hi, b0, b1), 12n)), U32.or(128, U32{W.join(6n, 26n, W.adjust(6n, 32n, bits(U32.shrn(scalar3(hi, b0, b1), 6n))), Word.zero(26n))}), U32.or(128, _)] == [U32{W.join(4n, 28n, hi, W.adjust(28n, 32n, bits(14)))}, continuation(b0), continuation(b1)] : List<&2, U32>}
      {==}

def scalar4(hi: Word(3n), b0: Word(6n), b1: Word(6n), b2: Word(6n)) -> U32:
  U32{W.join(6n, 26n, b2, W.join(6n, 20n, b1, W.join(6n, 14n, b0, W.join(3n, 11n, hi, Word.zero(11n)))))}

law utf8_form_4_bytes:
  for +hi: Word(3n)
  for +b0: Word(6n)
  for +b1: Word(6n)
  for +b2: Word(6n)
  {B.utf8_code_emit(scalar4(hi, b0, b1, b2), False{}, False{}, False{}) == [U32{W.join(3n, 29n, hi, W.adjust(29n, 32n, bits(30)))}, continuation(b0), continuation(b1), continuation(b2)] : List<&2, U32>}
def utf8_form_4_bytes(hi, b0, b1, b2):
  match hi b0 b1 b2:
    case WCon{+hi0, WCon{+hi1, WCon{+hi2, WNil{}}}} WCon{+b00, WCon{+b01, WCon{+b02, WCon{+b03, WCon{+b04, WCon{+b05, WNil{}}}}}}} WCon{+b10, WCon{+b11, WCon{+b12, WCon{+b13, WCon{+b14, WCon{+b15, WNil{}}}}}}} WCon{+b20, WCon{+b21, WCon{+b22, WCon{+b23, WCon{+b24, WCon{+b25, WNil{}}}}}}}:
      %Equal.sym(U32, U32.and(U32.shrn(scalar4(hi, b0, b1, b2), 12n), 63), U32{W.join(6n, 26n, W.adjust(6n, 32n, bits(U32.shrn(scalar4(hi, b0, b1, b2), 12n))), Word.zero(26n))}, mask_six_bits(U32.shrn(scalar4(hi, b0, b1, b2), 12n))) :
        {[U32.or(240, U32.shrn(scalar4(hi, b0, b1, b2), 18n)), U32.or(128, _), U32.or(128, U32.and(U32.shrn(scalar4(hi, b0, b1, b2), 6n), 63)), U32.or(128, U32.and(scalar4(hi, b0, b1, b2), 63))] == [U32{W.join(3n, 29n, hi, W.adjust(29n, 32n, bits(30)))}, continuation(b0), continuation(b1), continuation(b2)] : List<&2, U32>}
      %Equal.sym(U32, U32.and(U32.shrn(scalar4(hi, b0, b1, b2), 6n), 63), U32{W.join(6n, 26n, W.adjust(6n, 32n, bits(U32.shrn(scalar4(hi, b0, b1, b2), 6n))), Word.zero(26n))}, mask_six_bits(U32.shrn(scalar4(hi, b0, b1, b2), 6n))) :
        {[U32.or(240, U32.shrn(scalar4(hi, b0, b1, b2), 18n)), U32.or(128, U32{W.join(6n, 26n, W.adjust(6n, 32n, bits(U32.shrn(scalar4(hi, b0, b1, b2), 12n))), Word.zero(26n))}), U32.or(128, _), U32.or(128, U32.and(scalar4(hi, b0, b1, b2), 63))] == [U32{W.join(3n, 29n, hi, W.adjust(29n, 32n, bits(30)))}, continuation(b0), continuation(b1), continuation(b2)] : List<&2, U32>}
      %Equal.sym(U32, U32.and(scalar4(hi, b0, b1, b2), 63), U32{W.join(6n, 26n, W.adjust(6n, 32n, bits(scalar4(hi, b0, b1, b2))), Word.zero(26n))}, mask_six_bits(scalar4(hi, b0, b1, b2))) :
        {[U32.or(240, U32.shrn(scalar4(hi, b0, b1, b2), 18n)), U32.or(128, U32{W.join(6n, 26n, W.adjust(6n, 32n, bits(U32.shrn(scalar4(hi, b0, b1, b2), 12n))), Word.zero(26n))}), U32.or(128, U32{W.join(6n, 26n, W.adjust(6n, 32n, bits(U32.shrn(scalar4(hi, b0, b1, b2), 6n))), Word.zero(26n))}), U32.or(128, _)] == [U32{W.join(3n, 29n, hi, W.adjust(29n, 32n, bits(30)))}, continuation(b0), continuation(b1), continuation(b2)] : List<&2, U32>}
      {==}

law priority_associative:
  for a: Cmp
  for b: Cmp
  for c: Cmp
  {O.priority(O.priority(a, b), c) == O.priority(a, O.priority(b, c)) : Cmp}
def priority_associative(a, b, c):
  match a:
    case EQ{}:
      {==}
    case LT{}:
      {==}
    case GT{}:
      {==}

law priority_equal_right:
  for c: Cmp
  {O.priority(c, EQ{}) == c : Cmp}
def priority_equal_right(c):
  match c:
    case EQ{}:
      {==}
    case LT{}:
      {==}
    case GT{}:
      {==}

law compare_blocks:
  for +k: Nat
  for +n: Nat
  for +a: Word(k)
  for +b: Word(k)
  for +x: Word(n)
  for +y: Word(n)
  {Word.cmp(Nat.add(k, n), W.join(k, n, a, x), W.join(k, n, b, y)) ==
    O.priority(Word.cmp(n, x, y), Word.cmp(k, a, b)) : Cmp}
def compare_blocks(k, n, a, b, x, y):
  match k:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          Equal.sym(Cmp, O.priority(Word.cmp(n, x, y), EQ{}), Word.cmp(n, x, y), priority_equal_right(Word.cmp(n, x, y)))
    case 1n+p:
      match a b:
        case WCon{+ah, +at} WCon{+bh, +bt}:
          %Equal.sym(Cmp,
            Word.cmp(Nat.add(p, n), W.join(p, n, at, x), W.join(p, n, bt, y)),
            O.priority(Word.cmp(n, x, y), Word.cmp(p, at, bt)), compare_blocks(p, n, at, bt, x, y)) :
            {Word.cmp.fin(ah, bh, _) == O.priority(Word.cmp(n, x, y), Word.cmp(1n+p, a, b)) : Cmp}
          Equal.trans(Cmp,
            Word.cmp.fin(ah, bh, O.priority(Word.cmp(n, x, y), Word.cmp(p, at, bt))),
            O.priority(O.priority(Word.cmp(n, x, y), Word.cmp(p, at, bt)), Bool.cmp(ah, bh)),
            O.priority(Word.cmp(n, x, y), Word.cmp(1n+p, a, b)),
            O.word_fin_priority(ah, bh, O.priority(Word.cmp(n, x, y), Word.cmp(p, at, bt))),
            Equal.trans(Cmp,
              O.priority(O.priority(Word.cmp(n, x, y), Word.cmp(p, at, bt)), Bool.cmp(ah, bh)),
              O.priority(Word.cmp(n, x, y), O.priority(Word.cmp(p, at, bt), Bool.cmp(ah, bh))),
              O.priority(Word.cmp(n, x, y), Word.cmp(1n+p, a, b)),
              priority_associative(Word.cmp(n, x, y), Word.cmp(p, at, bt), Bool.cmp(ah, bh)),
              Equal.cong(Cmp, Cmp, c => O.priority(Word.cmp(n, x, y), c),
                O.priority(Word.cmp(p, at, bt), Bool.cmp(ah, bh)), Word.cmp(1n+p, a, b),
                Equal.sym(Cmp, Word.cmp(1n+p, a, b), O.priority(Word.cmp(p, at, bt), Bool.cmp(ah, bh)), O.word_fin_priority(ah, bh, Word.cmp(p, at, bt))))))
