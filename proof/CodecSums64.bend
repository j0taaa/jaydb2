# Bridge between verified binary addition and actual codec functions.
import Base
import ../contract/Bytes.bend as B
import ../src/Codec.bend as C
import ./CodecCounters.bend as N
import ./CodecWordsWord.bend as W
import ./CodecSumsBits.bend as S

def bits(q: B.Number64) -> Word(64n):
  B.Number64{U32{hi}, U32{lo}} = q
  W.join(32n, 32n, lo, hi)

def represent(m: Maybe<&2, B.Number64>) -> Maybe<&2, Word(64n)>:
  match m:
    case None{}:
      None{}
    case Some{q}:
      Some{bits(q)}

def apply_carry(+n: Nat, c: Bool, m: Maybe<&2, Word(n)>) -> Maybe<&2, Word(n)>:
  match c:
    case False{}:
      m
    case True{}:
      S.increment(n, m)

law increment_end:
  for +n: Nat
  for +overflow: Bool
  for +w: Word(n)
  {S.increment(n, S.end(n, overflow, w)) == S.end(n, overflow || N.ones(n, w), Word.inc(n, w)) : Maybe<&2, Word(n)>}
def increment_end(n, overflow, w):
  match overflow:
    case False{}:
      {==}
    case True{}:
      {==}

law represent_sum_end:
  for +overflow: Bool
  for +hi: Word(32n)
  for +lo: Word(32n)
  {represent(C.sum64_end(overflow, U32{hi}, U32{lo})) == S.join_optional(32n, 32n, lo, S.end(32n, overflow, hi)) : Maybe<&2, Word(64n)>}
def represent_sum_end(overflow, hi, lo):
  match overflow:
    case False{}:
      {==}
    case True{}:
      {==}

law represent_sum_transport:
  for +c: Bool
  for +overflow: Bool
  for +hi: Word(32n)
  for +lo: Word(32n)
  {represent(C.sum64_transport(c, U32{hi}, U32{lo}, overflow)) ==
    S.join_optional(32n, 32n, lo, apply_carry(32n, c, S.end(32n, overflow, hi))) : Maybe<&2, Word(64n)>}
def represent_sum_transport(c, overflow, hi, lo):
  match c:
    case False{}:
      represent_sum_end(overflow, hi, lo)
    case True{}:
      %Equal.sym(Word(32n), Word.add(32n, hi, N.one(31n)), Word.inc(32n, hi), N.sum_one_increments(31n, hi)) :
        {represent(C.sum64_end(overflow || Cmp.is_eq(Word.cmp(32n, hi, N.maximum(32n))), U32{_}, U32{lo})) ==
          S.join_optional(32n, 32n, lo, S.increment(32n, S.end(32n, overflow, hi))) : Maybe<&2, Word(64n)>}
      %Equal.sym(Bool, Cmp.is_eq(Word.cmp(32n, hi, N.maximum(32n))), N.ones(32n, hi), N.comparison_maximum_recognizes_bits(32n, hi)) :
        {represent(C.sum64_end(overflow || _, U32{Word.inc(32n, hi)}, U32{lo})) ==
          S.join_optional(32n, 32n, lo, S.increment(32n, S.end(32n, overflow, hi))) : Maybe<&2, Word(64n)>}
      Equal.trans(Maybe<&2, Word(64n)>,
        represent(C.sum64_end(overflow || N.ones(32n, hi), U32{Word.inc(32n, hi)}, U32{lo})),
        S.join_optional(32n, 32n, lo, S.end(32n, overflow || N.ones(32n, hi), Word.inc(32n, hi))),
        S.join_optional(32n, 32n, lo, S.increment(32n, S.end(32n, overflow, hi))),
        represent_sum_end(overflow || N.ones(32n, hi), Word.inc(32n, hi), lo),
        Equal.cong(Maybe<&2, Word(32n)>, Maybe<&2, Word(64n)>, m => S.join_optional(32n, 32n, lo, m),
          S.end(32n, overflow || N.ones(32n, hi), Word.inc(32n, hi)), S.increment(32n, S.end(32n, overflow, hi)),
          Equal.sym(Maybe<&2, Word(32n)>, S.increment(32n, S.end(32n, overflow, hi)), S.end(32n, overflow || N.ones(32n, hi), Word.inc(32n, hi)), increment_end(32n, overflow, hi))))

law apply_carry_sum:
  for +n: Nat
  for +c: Bool
  for +a: Word(n)
  for +b: Word(n)
  {apply_carry(n, c, S.end(n, S.carry(n, a, b, False{}), Word.add(n, a, b))) == S.sum(n, a, b, c) : Maybe<&2, Word(n)>}
def apply_carry_sum(n, c, a, b):
  match c:
    case False{}:
      Equal.sym(Maybe<&2, Word(n)>, S.sum(n, a, b, False{}), S.end(n, S.carry(n, a, b, False{}), Word.add(n, a, b)), S.sum_exact(n, a, b, False{}))
    case True{}:
      Equal.trans(Maybe<&2, Word(n)>,
        S.increment(n, S.end(n, S.carry(n, a, b, False{}), Word.add(n, a, b))),
        S.increment(n, S.sum(n, a, b, False{})), S.sum(n, a, b, True{}),
        Equal.cong(Maybe<&2, Word(n)>, Maybe<&2, Word(n)>, m => S.increment(n, m),
          S.end(n, S.carry(n, a, b, False{}), Word.add(n, a, b)), S.sum(n, a, b, False{}),
          Equal.sym(Maybe<&2, Word(n)>, S.sum(n, a, b, False{}), S.end(n, S.carry(n, a, b, False{}), Word.add(n, a, b)), S.sum_exact(n, a, b, False{}))),
        Equal.sym(Maybe<&2, Word(n)>, S.sum(n, a, b, True{}), S.increment(n, S.sum(n, a, b, False{})), S.carry_initial_and_increment(n, a, b)))

# Structural equality for ALL Number64 pairs; receives no premise
# about the addition result.
law sum64_represents_sum_binary:
  for +a: B.Number64
  for +b: B.Number64
  {represent(C.sum64(a, b)) == S.sum(64n, bits(a), bits(b), False{}) : Maybe<&2, Word(64n)>}
def sum64_represents_sum_binary(a, b):
  match a b:
    case B.Number64{U32{+ah}, U32{+al}} B.Number64{U32{+bh}, U32{+bl}}:
      %S.carry_equivalent_comparison(32n, al, bl, False{}) :
        {represent(C.sum64_transport(_, U32{Word.add(32n, ah, bh)}, U32{Word.add(32n, al, bl)}, Cmp.is_lt(Word.cmp(32n, Word.add(32n, ah, bh), ah)))) ==
          S.sum(64n, W.join(32n, 32n, al, ah), W.join(32n, 32n, bl, bh), False{}) : Maybe<&2, Word(64n)>}
      %S.carry_equivalent_comparison(32n, ah, bh, False{}) :
        {represent(C.sum64_transport(S.carry(32n, al, bl, False{}), U32{Word.add(32n, ah, bh)}, U32{Word.add(32n, al, bl)}, _)) ==
          S.sum(64n, W.join(32n, 32n, al, ah), W.join(32n, 32n, bl, bh), False{}) : Maybe<&2, Word(64n)>}
      Equal.trans(Maybe<&2, Word(64n)>,
        represent(C.sum64_transport(S.carry(32n, al, bl, False{}), U32{Word.add(32n, ah, bh)}, U32{Word.add(32n, al, bl)}, S.carry(32n, ah, bh, False{}))),
        S.join_optional(32n, 32n, Word.add(32n, al, bl), apply_carry(32n, S.carry(32n, al, bl, False{}), S.end(32n, S.carry(32n, ah, bh, False{}), Word.add(32n, ah, bh)))),
        S.sum(64n, W.join(32n, 32n, al, ah), W.join(32n, 32n, bl, bh), False{}),
        represent_sum_transport(S.carry(32n, al, bl, False{}), S.carry(32n, ah, bh, False{}), Word.add(32n, ah, bh), Word.add(32n, al, bl)),
        Equal.trans(Maybe<&2, Word(64n)>,
          S.join_optional(32n, 32n, Word.add(32n, al, bl), apply_carry(32n, S.carry(32n, al, bl, False{}), S.end(32n, S.carry(32n, ah, bh, False{}), Word.add(32n, ah, bh)))),
          S.join_optional(32n, 32n, Word.add(32n, al, bl), S.sum(32n, ah, bh, S.carry(32n, al, bl, False{}))),
          S.sum(64n, W.join(32n, 32n, al, ah), W.join(32n, 32n, bl, bh), False{}),
          Equal.cong(Maybe<&2, Word(32n)>, Maybe<&2, Word(64n)>, m => S.join_optional(32n, 32n, Word.add(32n, al, bl), m),
            apply_carry(32n, S.carry(32n, al, bl, False{}), S.end(32n, S.carry(32n, ah, bh, False{}), Word.add(32n, ah, bh))),
            S.sum(32n, ah, bh, S.carry(32n, al, bl, False{})), apply_carry_sum(32n, S.carry(32n, al, bl, False{}), ah, bh)),
          Equal.sym(Maybe<&2, Word(64n)>, S.sum(64n, W.join(32n, 32n, al, ah), W.join(32n, 32n, bl, bh), False{}),
            S.join_optional(32n, 32n, Word.add(32n, al, bl), S.sum(32n, ah, bh, S.carry(32n, al, bl, False{}))), S.sum_blocks(32n, 32n, al, bl, ah, bh, False{}))))

law sum_optional_represents_sum_binary:
  for +a: Maybe<&2, B.Number64>
  for +b: Maybe<&2, B.Number64>
  {represent(C.sum_optional(a, b)) == S.sum_optional(64n, represent(a), represent(b)) : Maybe<&2, Word(64n)>}
def sum_optional_represents_sum_binary(a, b):
  match a b:
    case None{} _:
      {==}
    case Some{x} None{}:
      {==}
    case Some{+x} Some{+y}:
      sum64_represents_sum_binary(x, y)

law join_zeros:
  for +k: Nat
  for +n: Nat
  {W.join(k, n, Word.zero(k), Word.zero(n)) == Word.zero(Nat.add(k, n)) : Word(Nat.add(k, n))}
def join_zeros(k, n):
  match k:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), w => WCon{False{}, w},
        W.join(p, n, Word.zero(p), Word.zero(n)), Word.zero(Nat.add(p, n)), join_zeros(p, n))

law sum_carry_zero:
  for +n: Nat
  for +c: Bool
  for +a: Word(n)
  {S.sum(n, a, Word.zero(n), c) == apply_carry(n, c, Some{a}) : Maybe<&2, Word(n)>}
def sum_carry_zero(n, c, a):
  match c:
    case False{}:
      S.sum_zero_right(n, a)
    case True{}:
      S.sum_increment(n, a)

law sum_increment_blocks:
  for +k: Nat
  for +n: Nat
  for +lo: Word(k)
  for +hi: Word(n)
  {S.sum(Nat.add(k, n), W.join(k, n, lo, hi), Word.zero(Nat.add(k, n)), True{}) ==
    S.join_optional(k, n, Word.inc(k, lo), apply_carry(n, N.ones(k, lo), Some{hi})) : Maybe<&2, Word(Nat.add(k, n))>}
def sum_increment_blocks(k, n, lo, hi):
  %join_zeros(k, n) :
    {S.sum(Nat.add(k, n), W.join(k, n, lo, hi), _, True{}) ==
      S.join_optional(k, n, Word.inc(k, lo), apply_carry(n, N.ones(k, lo), Some{hi})) : Maybe<&2, Word(Nat.add(k, n))>}
  %N.adc_zero_increments(k, lo) :
    {S.sum(Nat.add(k, n), W.join(k, n, lo, hi), W.join(k, n, Word.zero(k), Word.zero(n)), True{}) ==
      S.join_optional(k, n, _, apply_carry(n, N.ones(k, lo), Some{hi})) : Maybe<&2, Word(Nat.add(k, n))>}
  %S.carry_increment(k, lo) :
    {S.sum(Nat.add(k, n), W.join(k, n, lo, hi), W.join(k, n, Word.zero(k), Word.zero(n)), True{}) ==
      S.join_optional(k, n, Word.adc(k, lo, Word.zero(k), False{}, True{}), apply_carry(n, _, Some{hi})) : Maybe<&2, Word(Nat.add(k, n))>}
  Equal.trans(Maybe<&2, Word(Nat.add(k, n))>,
    S.sum(Nat.add(k, n), W.join(k, n, lo, hi), W.join(k, n, Word.zero(k), Word.zero(n)), True{}),
    S.join_optional(k, n, Word.adc(k, lo, Word.zero(k), False{}, True{}), S.sum(n, hi, Word.zero(n), S.carry(k, lo, Word.zero(k), True{}))),
    S.join_optional(k, n, Word.adc(k, lo, Word.zero(k), False{}, True{}), apply_carry(n, S.carry(k, lo, Word.zero(k), True{}), Some{hi})),
    S.sum_blocks(k, n, lo, Word.zero(k), hi, Word.zero(n), True{}),
    Equal.cong(Maybe<&2, Word(n)>, Maybe<&2, Word(Nat.add(k, n))>, m => S.join_optional(k, n, Word.adc(k, lo, Word.zero(k), False{}, True{}), m),
      S.sum(n, hi, Word.zero(n), S.carry(k, lo, Word.zero(k), True{})), apply_carry(n, S.carry(k, lo, Word.zero(k), True{}), Some{hi}),
      sum_carry_zero(n, S.carry(k, lo, Word.zero(k), True{}), hi)))

law increment_blocks:
  for +k: Nat
  for +n: Nat
  for +lo: Word(k)
  for +hi: Word(n)
  {S.increment(Nat.add(k, n), Some{W.join(k, n, lo, hi)}) ==
    S.join_optional(k, n, Word.inc(k, lo), apply_carry(n, N.ones(k, lo), Some{hi})) : Maybe<&2, Word(Nat.add(k, n))>}
def increment_blocks(k, n, lo, hi):
  Equal.trans(Maybe<&2, Word(Nat.add(k, n))>,
    S.increment(Nat.add(k, n), Some{W.join(k, n, lo, hi)}),
    S.sum(Nat.add(k, n), W.join(k, n, lo, hi), Word.zero(Nat.add(k, n)), True{}),
    S.join_optional(k, n, Word.inc(k, lo), apply_carry(n, N.ones(k, lo), Some{hi})),
    Equal.sym(Maybe<&2, Word(Nat.add(k, n))>,
      S.sum(Nat.add(k, n), W.join(k, n, lo, hi), Word.zero(Nat.add(k, n)), True{}),
      S.increment(Nat.add(k, n), Some{W.join(k, n, lo, hi)}), S.sum_increment(Nat.add(k, n), W.join(k, n, lo, hi))),
    sum_increment_blocks(k, n, lo, hi))

def represent_increment_cases(transport: Bool, exhausted: Bool, +hi: Word(32n), +lo: Word(32n),
  link: {N.ones(32n, lo) == transport : Bool},
  ehi: {N.ones(32n, hi) == exhausted : Bool}) ->
  {represent(B.increment64_cases(U32{hi}, U32{lo}, transport, exhausted)) ==
    S.join_optional(32n, 32n, Word.inc(32n, lo), apply_carry(32n, transport, Some{hi})) : Maybe<&2, Word(64n)>}:
  match transport exhausted:
    case False{} _:
      Equal.cong(Word(32n), Maybe<&2, Word(64n)>, w => Some{W.join(32n, 32n, w, hi)},
        Word.add(32n, lo, N.one(31n)), Word.inc(32n, lo), N.sum_one_increments(31n, lo))
    case True{} False{}:
      %Equal.sym(Bool, N.ones(32n, hi), False{}, ehi) :
        {Some{W.join(32n, 32n, Word.zero(32n), Word.add(32n, hi, N.one(31n)))} ==
          S.join_optional(32n, 32n, Word.inc(32n, lo), S.end(32n, _, Word.inc(32n, hi))) : Maybe<&2, Word(64n)>}
      %S.increment_maximum_zero(32n, lo, link) :
        {Some{W.join(32n, 32n, _, Word.add(32n, hi, N.one(31n)))} ==
          Some{W.join(32n, 32n, Word.inc(32n, lo), Word.inc(32n, hi))} : Maybe<&2, Word(64n)>}
      Equal.cong(Word(32n), Maybe<&2, Word(64n)>, w => Some{W.join(32n, 32n, Word.inc(32n, lo), w)},
        Word.add(32n, hi, N.one(31n)), Word.inc(32n, hi), N.sum_one_increments(31n, hi))
    case True{} True{}:
      %Equal.sym(Bool, N.ones(32n, hi), True{}, ehi) :
        {None{} == S.join_optional(32n, 32n, Word.inc(32n, lo), S.end(32n, _, Word.inc(32n, hi))) : Maybe<&2, Word(64n)>}
      {==}

law increment64_represents_increment_binary:
  for +m: Maybe<&2, B.Number64>
  {represent(B.increment64(m)) == S.increment(64n, represent(m)) : Maybe<&2, Word(64n)>}
def increment64_represents_increment_binary(m):
  match m:
    case None{}:
      {==}
    case Some{B.Number64{U32{+hi}, U32{+lo}}}:
      %Equal.sym(Bool, Cmp.is_eq(Word.cmp(32n, lo, N.maximum(32n))), N.ones(32n, lo), N.comparison_maximum_recognizes_bits(32n, lo)) :
        {represent(B.increment64_cases(U32{hi}, U32{lo}, _, Cmp.is_eq(Word.cmp(32n, hi, N.maximum(32n))))) ==
          S.increment(64n, Some{W.join(32n, 32n, lo, hi)}) : Maybe<&2, Word(64n)>}
      %Equal.sym(Bool, Cmp.is_eq(Word.cmp(32n, hi, N.maximum(32n))), N.ones(32n, hi), N.comparison_maximum_recognizes_bits(32n, hi)) :
        {represent(B.increment64_cases(U32{hi}, U32{lo}, N.ones(32n, lo), _)) ==
          S.increment(64n, Some{W.join(32n, 32n, lo, hi)}) : Maybe<&2, Word(64n)>}
      Equal.trans(Maybe<&2, Word(64n)>,
        represent(B.increment64_cases(U32{hi}, U32{lo}, N.ones(32n, lo), N.ones(32n, hi))),
        S.join_optional(32n, 32n, Word.inc(32n, lo), apply_carry(32n, N.ones(32n, lo), Some{hi})),
        S.increment(64n, Some{W.join(32n, 32n, lo, hi)}),
        represent_increment_cases(N.ones(32n, lo), N.ones(32n, hi), hi, lo, {==}, {==}),
        Equal.sym(Maybe<&2, Word(64n)>, S.increment(64n, Some{W.join(32n, 32n, lo, hi)}),
          S.join_optional(32n, 32n, Word.inc(32n, lo), apply_carry(32n, N.ones(32n, lo), Some{hi})), increment_blocks(32n, 32n, lo, hi)))

law nat64_represents_natural_binary:
  for +n: Nat
  {represent(B.nat64(n)) == S.natural(64n, n) : Maybe<&2, Word(64n)>}
def nat64_represents_natural_binary(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Maybe<&2, Word(64n)>,
        represent(B.increment64(B.nat64(p))), S.increment(64n, represent(B.nat64(p))), S.increment(64n, S.natural(64n, p)),
        increment64_represents_increment_binary(B.nat64(p)),
        Equal.cong(Maybe<&2, Word(64n)>, Maybe<&2, Word(64n)>, m => S.increment(64n, m),
          represent(B.nat64(p)), S.natural(64n, p), nat64_represents_natural_binary(p)))

# Structural projections used only to show bridge faithfulness.
def low(k: Nat, -n: Nat, w: Word(Nat.add(k, n))) -> Word(k):
  match k:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          WCon{b, low(p, n, t)}

def high(k: Nat, -n: Nat, w: Word(Nat.add(k, n))) -> Word(n):
  match k:
    case 0n:
      w
    case 1n+p:
      match w:
        case WCon{b, t}:
          high(p, n, t)

law low_join:
  for +k: Nat
  for +n: Nat
  for +lo: Word(k)
  for +hi: Word(n)
  {low(k, n, W.join(k, n, lo, hi)) == lo : Word(k)}
def low_join(k, n, lo, hi):
  match k:
    case 0n:
      match lo:
        case WNil{}:
          {==}
    case 1n+p:
      match lo:
        case WCon{b, +t}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{b, w}, low(p, n, W.join(p, n, t, hi)), t, low_join(p, n, t, hi))

law high_join:
  for +k: Nat
  for +n: Nat
  for +lo: Word(k)
  for +hi: Word(n)
  {high(k, n, W.join(k, n, lo, hi)) == hi : Word(n)}
def high_join(k, n, lo, hi):
  match k:
    case 0n:
      {==}
    case 1n+p:
      match lo:
        case WCon{b, t}:
          high_join(p, n, t, hi)

def recover_bits(+w: Word(64n)) -> B.Number64:
  B.Number64{U32{high(32n, 32n, w)}, U32{low(32n, 32n, w)}}

def recover(m: Maybe<&2, Word(64n)>) -> Maybe<&2, B.Number64>:
  match m:
    case None{}:
      None{}
    case Some{w}:
      Some{recover_bits(w)}

law recover_bits_exact:
  for +q: B.Number64
  {recover_bits(bits(q)) == q : B.Number64}
def recover_bits_exact(q):
  match q:
    case B.Number64{U32{+hi}, U32{+lo}}:
      %Equal.sym(Word(32n), high(32n, 32n, W.join(32n, 32n, lo, hi)), hi, high_join(32n, 32n, lo, hi)) :
        {B.Number64{U32{_}, U32{low(32n, 32n, W.join(32n, 32n, lo, hi))}} == B.Number64{U32{hi}, U32{lo}} : B.Number64}
      Equal.cong(Word(32n), B.Number64, w => B.Number64{U32{hi}, U32{w}},
        low(32n, 32n, W.join(32n, 32n, lo, hi)), lo, low_join(32n, 32n, lo, hi))

law recover_represent:
  for +m: Maybe<&2, B.Number64>
  {recover(represent(m)) == m : Maybe<&2, B.Number64>}
def recover_represent(m):
  match m:
    case None{}:
      {==}
    case Some{+q}:
      Equal.cong(B.Number64, Maybe<&2, B.Number64>, x => Some{x}, recover_bits(bits(q)), q, recover_bits_exact(q))

law represent_injective:
  for +a: Maybe<&2, B.Number64>
  for +b: Maybe<&2, B.Number64>
  for e: {represent(a) == represent(b) : Maybe<&2, Word(64n)>}
  {a == b : Maybe<&2, B.Number64>}
def represent_injective(a, b, e):
  Equal.trans(Maybe<&2, B.Number64>, a, recover(represent(a)), b,
    Equal.sym(Maybe<&2, B.Number64>, recover(represent(a)), a, recover_represent(a)),
    Equal.trans(Maybe<&2, B.Number64>, recover(represent(a)), recover(represent(b)), b,
      Equal.cong(Maybe<&2, Word(64n)>, Maybe<&2, B.Number64>, m => recover(m), represent(a), represent(b), e),
      recover_represent(b)))

law sum_naturals_represented:
  for +n: Nat
  for +m: Nat
  {S.sum_optional(64n, represent(B.nat64(n)), represent(B.nat64(m))) == S.natural(64n, Nat.add(n, m)) : Maybe<&2, Word(64n)>}
def sum_naturals_represented(n, m):
  %Equal.sym(Maybe<&2, Word(64n)>, represent(B.nat64(n)), S.natural(64n, n), nat64_represents_natural_binary(n)) :
    {S.sum_optional(64n, _, represent(B.nat64(m))) == S.natural(64n, Nat.add(n, m)) : Maybe<&2, Word(64n)>}
  %Equal.sym(Maybe<&2, Word(64n)>, represent(B.nat64(m)), S.natural(64n, m), nat64_represents_natural_binary(m)) :
    {S.sum_optional(64n, S.natural(64n, n), _) == S.natural(64n, Nat.add(n, m)) : Maybe<&2, Word(64n)>}
  S.sum_naturals(64n, n, m)
