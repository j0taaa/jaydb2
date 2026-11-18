# Connect the worker's native Nat conversion to the canonical u64 word.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../src/Remote.bend as Remote
import ./CodecCanonical.bend as Canonical
import ./CodecRelaxArithmeticWord.bend as Measure
import ./CodecSums.bend as Sums
import ./CodecSums64.bend as Binary
import ./CodecCounters.bend as Counts
import ./CodecWordsWord.bend as Words

def scale(n: Nat, x: Nat) -> Nat:
  match n:
    case 0n: x
    case 1n+ +p: Nat.double(scale(p, x))

law double_sum:
  for a: Nat
  for +b: Nat
  {Nat.double(Nat.add(a, b)) == Nat.add(Nat.double(a), Nat.double(b)) : Nat}
def double_sum(a, b):
  match a:
    case 0n: {==}
    case 1n+ +p:
      Equal.cong(Nat, Nat, n => 2n+n, Nat.double(Nat.add(p, b)),
        Nat.add(Nat.double(p), Nat.double(b)), double_sum(p, b))

law double_product:
  for a: Nat
  for +b: Nat
  {Nat.double(Nat.mul(a, b)) == Nat.mul(a, Nat.double(b)) : Nat}
def double_product(a, b):
  match a:
    case 0n: {==}
    case 1n+ +p:
      %Equal.sym(Nat, Nat.double(Nat.add(b, Nat.mul(p, b))),
        Nat.add(Nat.double(b), Nat.double(Nat.mul(p, b))), double_sum(b, Nat.mul(p, b))) : { _ == Nat.add(Nat.double(b), Nat.mul(p, Nat.double(b))) : Nat}
      Equal.cong(Nat, Nat, n => Nat.add(Nat.double(b), n),
        Nat.double(Nat.mul(p, b)), Nat.mul(p, Nat.double(b)), double_product(p, b))

law multiply_by_one:
  for a: Nat
  {Nat.mul(a, 1n) == a : Nat}
def multiply_by_one(a):
  match a:
    case 0n: {==}
    case 1n+ +p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.mul(p, 1n), p, multiply_by_one(p))

law multiply_by_power_of_two:
  for width: Nat
  for +a: Nat
  {Nat.mul(a, scale(width, 1n)) == scale(width, a) : Nat}
def multiply_by_power_of_two(width, a):
  match width:
    case 0n: multiply_by_one(a)
    case 1n+ +p:
      %double_product(a, scale(p, 1n)) : {_ == Nat.double(scale(p, a)) : Nat}
      Equal.cong(Nat, Nat, n => Nat.double(n),
        Nat.mul(a, scale(p, 1n)), scale(p, a), multiply_by_power_of_two(p, a))

def double_scaled(+x: Nat, +factor: Nat, +y: Nat) ->
  {Nat.double(Nat.add(Nat.mul(x, factor), y)) == Nat.add(Nat.mul(x, Nat.double(factor)), Nat.double(y)) : Nat}:
  %Equal.sym(Nat, Nat.double(Nat.add(Nat.mul(x, factor), y)),
    Nat.add(Nat.double(Nat.mul(x, factor)), Nat.double(y)), double_sum(Nat.mul(x, factor), y)) : {_ == Nat.add(Nat.mul(x, Nat.double(factor)), Nat.double(y)) : Nat}
  Equal.cong(Nat, Nat, n => Nat.add(n, Nat.double(y)),
    Nat.double(Nat.mul(x, factor)), Nat.mul(x, Nat.double(factor)), double_product(x, factor))

law joined_word_natural:
  for k: Nat
  for +n: Nat
  for lo: Word(k)
  for +hi: Word(n)
  {Word.to_nat(Nat.add(k, n), Words.join(k, n, lo, hi)) ==
    Nat.add(Nat.mul(Word.to_nat(n, hi), scale(k, 1n)), Word.to_nat(k, lo)) : Nat}
def joined_word_natural(k, n, lo, hi):
  match k:
    case 0n:
      %Equal.sym(Nat, Nat.mul(Word.to_nat(n, hi), 1n), Word.to_nat(n, hi),
        multiply_by_one(Word.to_nat(n, hi))) : {Word.to_nat(n, hi) == Nat.add(_, 0n) : Nat}
      Equal.sym(Nat, Nat.add(Word.to_nat(n, hi), 0n), Word.to_nat(n, hi), Sums.nat_sum_zero_right(Word.to_nat(n, hi)))
    case 1n+ +p:
      match lo:
        case WCon{False{}, +t}:
          %Equal.sym(Nat, Word.to_nat(Nat.add(p, n), Words.join(p, n, t, hi)),
            Nat.add(Nat.mul(Word.to_nat(n, hi), scale(p, 1n)), Word.to_nat(p, t)),
            joined_word_natural(p, n, t, hi)) : {Nat.double(_) ==
            Nat.add(Nat.mul(Word.to_nat(n, hi), Nat.double(scale(p, 1n))), Nat.double(Word.to_nat(p, t))) : Nat}
          double_scaled(Word.to_nat(n, hi), scale(p, 1n), Word.to_nat(p, t))
        case WCon{True{}, +t}:
          +factor = Nat.mul(Word.to_nat(n, hi), Nat.double(scale(p, 1n)))
          +tail = Nat.double(Word.to_nat(p, t))
          %Equal.sym(Nat, Nat.add(factor, 1n+tail), 1n+Nat.add(factor, tail),
            Canonical.sum_successor_right(factor, tail)) :
            {1n+Nat.double(Word.to_nat(Nat.add(p, n), Words.join(p, n, t, hi))) == _ : Nat}
          Equal.cong(Nat, Nat, v => 1n+v,
            Nat.double(Word.to_nat(Nat.add(p, n), Words.join(p, n, t, hi))), Nat.add(factor, tail),
            Equal.trans(Nat, Nat.double(Word.to_nat(Nat.add(p, n), Words.join(p, n, t, hi))),
              Nat.double(Nat.add(Nat.mul(Word.to_nat(n, hi), scale(p, 1n)), Word.to_nat(p, t))),
              Nat.add(factor, tail),
              Equal.cong(Nat, Nat, v => Nat.double(v),
                Word.to_nat(Nat.add(p, n), Words.join(p, n, t, hi)),
                Nat.add(Nat.mul(Word.to_nat(n, hi), scale(p, 1n)), Word.to_nat(p, t)),
                joined_word_natural(p, n, t, hi)),
              double_scaled(Word.to_nat(n, hi), scale(p, 1n), Word.to_nat(p, t))))

law measure_zeros_low:
  for k: Nat
  for +n: Nat
  for +w: Word(n)
  {Word.to_nat(Nat.add(k, n), Words.zeros_low(k, n, w)) == scale(k, Word.to_nat(n, w)) : Nat}
def measure_zeros_low(k, n, w):
  match k:
    case 0n: {==}
    case 1n+ +p:
      Equal.cong(Nat, Nat, v => Nat.double(v), Word.to_nat(Nat.add(p, n), Words.zeros_low(p, n, w)),
        scale(p, Word.to_nat(n, w)), measure_zeros_low(p, n, w))

law scale_add:
  for a: Nat
  for +b: Nat
  for +x: Nat
  {scale(a, scale(b, x)) == scale(Nat.add(a, b), x) : Nat}
def scale_add(a, b, x):
  match a:
    case 0n: {==}
    case 1n+ +p:
      Equal.cong(Nat, Nat, v => Nat.double(v), scale(p, scale(b, x)), scale(Nat.add(p, b), x),
        scale_add(p, b, x))

def half_word_from_bits(+value: U32, +word: Word(16n),
  bits: {value == U32{Words.zeros_low(16n, 16n, word)} : U32},
  one: {Word.to_nat(16n, word) == 1n : Nat}) ->
  {U32.to_nat(value) == scale(16n, 1n) : Nat}:
  %Equal.sym(U32, value, U32{Words.zeros_low(16n, 16n, word)}, bits) :
    {U32.to_nat(_) == scale(16n, 1n) : Nat}
  %one : {U32.to_nat(U32{Words.zeros_low(16n, 16n, word)}) == scale(16n, _) : Nat}
  measure_zeros_low(16n, 16n, word)

def half_word() -> {U32.to_nat(65536) == scale(16n, 1n) : Nat}:
  half_word_from_bits(65536, Words.one(16n), {==}, {==})

def squared_power_of_two(+width: Nat, +half: Nat, exact: {half == scale(width, 1n) : Nat}) ->
  {Nat.mul(half, half) == scale(Nat.add(width, width), 1n) : Nat}:
  %Equal.sym(Nat, half, scale(width, 1n), exact) :
    {Nat.mul(_, _) == scale(Nat.add(width, width), 1n) : Nat}
  Equal.trans(Nat, Nat.mul(scale(width, 1n), scale(width, 1n)), scale(width, scale(width, 1n)),
    scale(Nat.add(width, width), 1n),
    multiply_by_power_of_two(width, scale(width, 1n)), scale_add(width, width, 1n))

def width_sum() -> {Nat.add(16n, 16n) == 32n : Nat}:
  {==}

def word_factor() -> {Nat.mul(U32.to_nat(65536), U32.to_nat(65536)) == scale(32n, 1n) : Nat}:
  %width_sum() :
    {Nat.mul(U32.to_nat(65536), U32.to_nat(65536)) == scale(_, 1n) : Nat}
  squared_power_of_two(16n, U32.to_nat(65536), half_word())

def count_has_measure(+high: U32, +low: U32, +radix: Nat, +n: Nat,
  measure: {Nat.add(Nat.mul(U32.to_nat(high), radix), U32.to_nat(low)) == n : Nat}) ->
  {Remote.count_words(high, low, radix) == Some{S.Datum{D.Count{n}}} : Maybe<&2, S.Return>}:
  Equal.cong(Nat, Maybe<&2, S.Return>, v => Some{S.Datum{D.Count{v}}},
    Nat.add(Nat.mul(U32.to_nat(high), radix), U32.to_nat(low)), n, measure)

def measured_join(+k: Nat, +m: Nat, +lo: Word(k), +hi: Word(m), +n: Nat,
  measure: {Word.to_nat(Nat.add(k, m), Words.join(k, m, lo, hi)) == n : Nat}) ->
  {Nat.add(Nat.mul(Word.to_nat(m, hi), scale(k, 1n)), Word.to_nat(k, lo)) == n : Nat}:
  +joined = Word.to_nat(Nat.add(k, m), Words.join(k, m, lo, hi))
  +parts = Nat.add(Nat.mul(Word.to_nat(m, hi), scale(k, 1n)), Word.to_nat(k, lo))
  Equal.trans(Nat, parts, joined, n,
    Equal.sym(Nat, joined, parts, joined_word_natural(k, m, lo, hi)), measure)

def number_word_decodes(+high: U32, +low: U32, +n: Nat,
  measure: {B.nat64(n) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>}) ->
  {Word.to_nat(64n, Binary.bits(B.Number64{high, low})) == n : Nat}:
  Counts.nat64_and_injective_in_results_representable(
    Word.to_nat(64n, Binary.bits(B.Number64{high, low})), n, B.Number64{high, low},
    Measure.nat64_measures_number(B.Number64{high, low}), measure)

def count_has_word_measure(+hi: Word(32n), +lo: Word(32n), +radix: Nat, +n: Nat,
  measure: {Nat.add(Nat.mul(Word.to_nat(32n, hi), radix), Word.to_nat(32n, lo)) == n : Nat}) ->
  {Remote.count_words(U32{hi}, U32{lo}, radix) == Some{S.Datum{D.Count{n}}} : Maybe<&2, S.Return>}:
  count_has_measure(U32{hi}, U32{lo}, radix, n, measure)

def count_at_scale(+high: U32, +low: U32, +n: Nat,
  measured: {B.nat64(n) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>}) ->
  {Remote.count_words(high, low, scale(32n, 1n)) == Some{S.Datum{D.Count{n}}} : Maybe<&2, S.Return>}:
  match high low:
    case U32{+hi} U32{+lo}:
      count_has_word_measure(hi, lo, scale(32n, 1n), n,
        measured_join(32n, 32n, lo, hi, n, number_word_decodes(U32{hi}, U32{lo}, n, measured)))

def counted_number(+high: U32, +low: U32, +n: Nat, +radix: Nat,
  measured: {B.nat64(n) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>},
  factor: {radix == scale(32n, 1n) : Nat}) ->
  {Remote.count_words(high, low, radix) == Some{S.Datum{D.Count{n}}} : Maybe<&2, S.Return>}:
  %Equal.sym(Nat, radix, scale(32n, 1n), factor) :
    {Remote.count_words(high, low, _) == Some{S.Datum{D.Count{n}}} : Maybe<&2, S.Return>}
  count_at_scale(high, low, n, measured)

def count_for_half(+high: U32, +low: U32, +n: Nat, +half: U32,
  measured: {B.nat64(n) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>},
  factor: {Nat.mul(U32.to_nat(half), U32.to_nat(half)) == scale(32n, 1n) : Nat}) ->
  {Remote.count(True{}, high, low, half) == Some{S.Datum{D.Count{n}}} : Maybe<&2, S.Return>}:
  counted_number(high, low, n, Nat.mul(U32.to_nat(half), U32.to_nat(half)), measured, factor)

law count_decodes_exact_natural:
  for +high: U32
  for +low: U32
  for +n: Nat
  for measured: {B.nat64(n) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>}
  {Remote.count(True{}, high, low, 65536) == Some{S.Datum{D.Count{n}}} : Maybe<&2, S.Return>}
def count_decodes_exact_natural(high, low, n, measured):
  count_for_half(high, low, n, 65536, measured, word_factor())
