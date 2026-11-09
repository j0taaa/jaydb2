# No arithmetic axiom or finite-input premise: commute one genuine contract
# increment through the tail traversal, then recover the original conversion.
import Base
import ../contract/Bytes.bend as B
import ../src/FastBytes.bend as F
import ./Foundations.bend as H
import ./CodecWordsWord.bend as W
import ./CodecSums64.bend as P
import ./CodecRelaxArithmeticWord.bend as R

law advance_commutes_with_increment:
  for +n: Nat
  for +value: Maybe<&2, B.Number64>
  {F.advance(n, B.increment64(value)) == B.increment64(F.advance(n, value)) : Maybe<&2, B.Number64>}
def advance_commutes_with_increment(n, value):
  match n:
    case 0n:
      {==}
    case 1n+p:
      advance_commutes_with_increment(p, B.increment64(value))

law nat64_exact:
  for +n: Nat
  {F.nat64(n) == B.nat64(n) : Maybe<&2, B.Number64>}
def nat64_exact(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Maybe<&2, B.Number64>,
        F.advance(p, B.increment64(F.zero())),
        B.increment64(F.advance(p, F.zero())),
        B.increment64(B.nat64(p)),
        advance_commutes_with_increment(p, F.zero()),
        Equal.cong(Maybe<&2, B.Number64>, Maybe<&2, B.Number64>, B.increment64,
          F.nat64(p), B.nat64(p), nat64_exact(p)))

law length64_exact:
  for +n: Nat
  {F.length64(n) == B.length64(n) : Maybe<&2, List<&2, U32>>}
def length64_exact(n):
  Equal.cong(Maybe<&2, B.Number64>, Maybe<&2, List<&2, U32>>,
    B.number64_bytes, F.nat64(n), B.nat64(n), nat64_exact(n))

law natural_equal_reflects:
  for +a: Nat
  for +b: Nat
  for equal: {Nat.is_eq(a, b) == True{} : Bool}
  {a == b : Nat}
def natural_equal_reflects(a, b, equal):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      H.absurd_boolean({0n == 1n+bp : Nat}, equal)
    case 1n+ap 0n:
      H.absurd_boolean({1n+ap == 0n : Nat}, equal)
    case 1n+ap 1n+bp:
      Equal.cong(Nat, Nat, x => 1n+x, ap, bp, natural_equal_reflects(ap, bp, equal))

law zero_word_natural:
  for +n: Nat
  {Word.to_nat(n, Word.zero(n)) == 0n : Nat}
def zero_word_natural(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, Nat.double, Word.to_nat(p, Word.zero(p)), 0n,
        zero_word_natural(p))

law zero_high_preserves_natural:
  for +k: Nat
  for +n: Nat
  for +low: Word(k)
  {Word.to_nat(Nat.add(k, n), W.join(k, n, low, Word.zero(n))) == Word.to_nat(k, low) : Nat}
def zero_high_preserves_natural(k, n, low):
  match k:
    case 0n:
      zero_word_natural(n)
    case 1n+p:
      match low:
        case WCon{False{}, tail}:
          Equal.cong(Nat, Nat, Nat.double,
            Word.to_nat(Nat.add(p, n), W.join(p, n, tail, Word.zero(n))),
            Word.to_nat(p, tail), zero_high_preserves_natural(p, n, tail))
        case WCon{True{}, tail}:
          Equal.cong(Nat, Nat, x => 1n+Nat.double(x),
            Word.to_nat(Nat.add(p, n), W.join(p, n, tail, Word.zero(n))),
            Word.to_nat(p, tail), zero_high_preserves_natural(p, n, tail))

law word32_measured_exactly:
  for +word: U32
  {B.nat64(U32.to_nat(word)) == Some{B.Number64{0, word}} : Maybe<&2, B.Number64>}
def word32_measured_exactly(word):
  match word:
    case U32{bits}:
      %zero_high_preserves_natural(32n, 32n, bits) :
        {B.nat64(_) == Some{B.Number64{0, U32{bits}}} : Maybe<&2, B.Number64>}
      R.nat64_measures_number(B.Number64{0, U32{bits}})

# All arithmetic remains proved in the source language. The runtime shift
# has fixed width32; no division or machine-cast correctness axiom is assumed.
law double_add:
  for +a: Nat
  for +b: Nat
  {Nat.double(Nat.add(a, b)) == Nat.add(Nat.double(a), Nat.double(b)) : Nat}
def double_add(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 2n+x,
        Nat.double(Nat.add(p, b)), Nat.add(Nat.double(p), Nat.double(b)),
        double_add(p, b))

law double_sum_from_equal:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for equal: {a == Nat.add(b, c) : Nat}
  {Nat.double(a) == Nat.add(Nat.double(b), Nat.double(c)) : Nat}
def double_sum_from_equal(a, b, c, equal):
  Equal.trans(Nat, Nat.double(a), Nat.double(Nat.add(b, c)),
    Nat.add(Nat.double(b), Nat.double(c)),
    Equal.cong(Nat, Nat, Nat.double, a, Nat.add(b, c), equal),
    double_add(b, c))

law join_measure:
  for +k: Nat
  for +n: Nat
  for +low: Word(k)
  for +high: Word(n)
  {Word.to_nat(Nat.add(k, n), W.join(k, n, low, high)) ==
    Nat.add(Word.to_nat(k, low), F.shift(k, Word.to_nat(n, high))) : Nat}
def join_measure(k, n, low, high):
  match k:
    case 0n:
      match low:
        case WNil{}:
          {==}
    case 1n+p:
      match low:
        case WCon{False{}, tail}:
          double_sum_from_equal(
            Word.to_nat(Nat.add(p, n), W.join(p, n, tail, high)),
            Word.to_nat(p, tail), F.shift(p, Word.to_nat(n, high)),
            join_measure(p, n, tail, high))
        case WCon{True{}, tail}:
          Equal.cong(Nat, Nat, x => 1n+x,
            Nat.double(Word.to_nat(Nat.add(p, n), W.join(p, n, tail, high))),
            Nat.add(Nat.double(Word.to_nat(p, tail)), Nat.double(F.shift(p, Word.to_nat(n, high)))),
            double_sum_from_equal(
              Word.to_nat(Nat.add(p, n), W.join(p, n, tail, high)),
              Word.to_nat(p, tail), F.shift(p, Word.to_nat(n, high)),
              join_measure(p, n, tail, high)))

law measure_exact:
  for +number: B.Number64
  {F.measure(number) == Word.to_nat(64n, P.bits(number)) : Nat}
def measure_exact(number):
  match number:
    case B.Number64{U32{high}, U32{low}}:
      Equal.sym(Nat,
        Word.to_nat(64n, W.join(32n, 32n, low, high)),
        Nat.add(Word.to_nat(32n, low), F.shift(32n, Word.to_nat(32n, high))),
        join_measure(32n, 32n, low, high))

law measured_candidate_exact:
  for +number: B.Number64
  {B.nat64(F.measure(number)) == Some{number} : Maybe<&2, B.Number64>}
def measured_candidate_exact(number):
  %Equal.sym(Nat, F.measure(number), Word.to_nat(64n, P.bits(number)), measure_exact(number)) :
    {B.nat64(_) == Some{number} : Maybe<&2, B.Number64>}
  R.nat64_measures_number(number)

law checked64_exact:
  for +n: Nat
  for +number: B.Number64
  for roundtrip: Bool
  for valid: {Nat.is_eq(F.measure(number), n) == roundtrip : Bool}
  {F.checked64(n, number, roundtrip) == B.nat64(n) : Maybe<&2, B.Number64>}
def checked64_exact(n, number, roundtrip, valid):
  match roundtrip:
    case False{}:
      nat64_exact(n)
    case True{}:
      %natural_equal_reflects(F.measure(number), n, valid) :
        {Some{number} == B.nat64(_) : Maybe<&2, B.Number64>}
      Equal.sym(Maybe<&2, B.Number64>, B.nat64(F.measure(number)),
        Some{number}, measured_candidate_exact(number))

law nat64_wide_exact:
  for +n: Nat
  {F.nat64_wide(n) == B.nat64(n) : Maybe<&2, B.Number64>}
def nat64_wide_exact(n):
  checked64_exact(n, F.candidate(n), Nat.is_eq(F.measure(F.candidate(n)), n), {==})

law checked32_exact:
  for +n: Nat
  for +word: U32
  for roundtrip: Bool
  for valid: {Nat.is_eq(U32.to_nat(word), n) == roundtrip : Bool}
  {F.checked32(n, word, roundtrip) == B.nat64(n) : Maybe<&2, B.Number64>}
def checked32_exact(n, word, roundtrip, valid):
  match roundtrip:
    case False{}:
      nat64_wide_exact(n)
    case True{}:
      %natural_equal_reflects(U32.to_nat(word), n, valid) :
        {Some{B.Number64{0, word}} == B.nat64(_) : Maybe<&2, B.Number64>}
      Equal.sym(Maybe<&2, B.Number64>, B.nat64(U32.to_nat(word)),
        Some{B.Number64{0, word}}, word32_measured_exactly(word))

law nat64_checked_exact:
  for +n: Nat
  {F.nat64_checked(n) == B.nat64(n) : Maybe<&2, B.Number64>}
def nat64_checked_exact(n):
  checked32_exact(n, U32.from_nat(n), Nat.is_eq(U32.to_nat(U32.from_nat(n)), n), {==})
