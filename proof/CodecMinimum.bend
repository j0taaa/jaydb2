# Bound/minimum algebra: lemmas about the actual implementation.
import Base
import ../contract/Bytes.bend as B
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./Orders.bend as O
import ./CodecCounters.bend as N
import ./CodecUnicode.bend as U
import ./CodecWordsWord.bend as W
import ./CodecWordsBE64.bend as H
import ./CodecUTF8Bits.bend as A
import ./CodecTrace.bend as R

law sum_zero_u32:
  for +x: U32
  {(x + 0 : U32) == x : U32}
def sum_zero_u32(x):
  match x:
    case U32{+w}:
      Equal.cong(Word(32n), U32, r => U32{r}, Word.add(32n, w, Word.zero(32n)), w, N.adc_zero_identity(32n, w))

law less_equal64_reflexive:
  for +n: B.Number64
  {C.less_equal64(n, n) == True{} : Bool}
def less_equal64_reflexive(n):
  match n:
    case B.Number64{+a, +b}:
      %Equal.sym(Cmp, U32.cmp(a, a), EQ{}, O.u32_refl(a)) :
        {Cmp.is_lt(_) || (Cmp.is_eq(U32.cmp(a, a)) && U32.is_le(b, b)) == True{} : Bool}
      %Equal.sym(Cmp, U32.cmp(a, a), EQ{}, O.u32_refl(a)) :
        {False{} || (Cmp.is_eq(_) && U32.is_le(b, b)) == True{} : Bool}
      Equal.cong(Cmp, Bool, c => Cmp.is_le(c), U32.cmp(b, b), EQ{}, O.u32_refl(b))

law sum64_zero_right:
  for +n: B.Number64
  {C.sum64(n, B.Number64{0, 0}) == Some{n} : Maybe<&2, B.Number64>}
def sum64_zero_right(n):
  match n:
    case B.Number64{+a, +b}:
      %Equal.sym(U32, (b + 0 : U32), b, sum_zero_u32(b)) :
        {C.sum64_transport(U32.is_lt(_, b), (a + 0 : U32), (b + 0 : U32), U32.is_lt((a + 0 : U32), a)) == Some{B.Number64{a, b}} : Maybe<&2, B.Number64>}
      %Equal.sym(U32, (a + 0 : U32), a, sum_zero_u32(a)) :
        {C.sum64_transport(U32.is_lt(b, b), _, (b + 0 : U32), U32.is_lt((a + 0 : U32), a)) == Some{B.Number64{a, b}} : Maybe<&2, B.Number64>}
      %Equal.sym(U32, (b + 0 : U32), b, sum_zero_u32(b)) :
        {C.sum64_transport(U32.is_lt(b, b), a, _, U32.is_lt((a + 0 : U32), a)) == Some{B.Number64{a, b}} : Maybe<&2, B.Number64>}
      %Equal.sym(U32, (a + 0 : U32), a, sum_zero_u32(a)) :
        {C.sum64_transport(U32.is_lt(b, b), a, b, U32.is_lt(_, a)) == Some{B.Number64{a, b}} : Maybe<&2, B.Number64>}
      %Equal.sym(Cmp, U32.cmp(b, b), EQ{}, O.u32_refl(b)) :
        {C.sum64_transport(Cmp.is_lt(_), a, b, U32.is_lt(a, a)) == Some{B.Number64{a, b}} : Maybe<&2, B.Number64>}
      %Equal.sym(Cmp, U32.cmp(a, a), EQ{}, O.u32_refl(a)) :
        {C.sum64_transport(False{}, a, b, Cmp.is_lt(_)) == Some{B.Number64{a, b}} : Maybe<&2, B.Number64>}
      {==}

law minimum_textual_in_root_and_exactly_to_count:
  for +q: B.Number64
  {C.sum_optional(C.minimum_field(C.TextValue{}, q), C.minimum_stack(C.Root{})) == Some{q} : Maybe<&2, B.Number64>}
def minimum_textual_in_root_and_exactly_to_count(q):
  sum64_zero_right(q)

law check_minimum_equal_to_body_allows_limit:
  for +body: B.Number64
  for +ceiling: B.Number64
  for fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  {C.check(Some{body}, body, ceiling) == C.Fits{} : C.Check}
def check_minimum_equal_to_body_allows_limit(body, ceiling, fits):
  %Equal.sym(Bool, C.less_equal64(body, ceiling), True{}, fits) :
    {C.check_cases(_, C.less_equal64(body, body)) == C.Fits{} : C.Check}
  %Equal.sym(Bool, C.less_equal64(body, body), True{}, less_equal64_reflexive(body)) :
    {C.check_cases(True{}, _) == C.Fits{} : C.Check}
  {==}

# This equivalence relates the successor carry flag to the exact
# maximum test; useful without converting any word to Nat.
law without_transport_equivalent_to_negative_maximum:
  for +n: Nat
  for +w: Word(n)
  {U.without_transport(n, w) == Bool.not(N.ones(n, w)) : Bool}
def without_transport_equivalent_to_negative_maximum(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          {==}
        case WCon{True{}, t}:
          without_transport_equivalent_to_negative_maximum(p, t)

law predecessor_positive_can_be_incremented:
  for +n: Nat
  for +w: Word(n)
  for negative_zero: {N.zeros(n, w) == False{} : Bool}
  {U.without_transport(n, N.predecessor(n, w)) == True{} : Bool}
def predecessor_positive_can_be_incremented(n, w, negative_zero):
  Equal.trans(Bool, U.without_transport(n, N.predecessor(n, w)), Bool.not(N.ones(n, N.predecessor(n, w))), True{},
    without_transport_equivalent_to_negative_maximum(n, N.predecessor(n, w)),
    Equal.cong(Bool, Bool, b => Bool.not(b), N.ones(n, N.predecessor(n, w)), False{},
      Equal.trans(Bool, N.ones(n, N.predecessor(n, w)), N.zeros(n, w), False{}, N.predecessor_maximum_exactly_in_zero(n, w), negative_zero)))

law compare_combined_predecessor_positive:
  for +n: Nat
  for +z: Word(n)
  for +w: Word(n)
  for negative_zero: {N.zeros(n, w) == False{} : Bool}
  {Cmp.is_le(Word.cmp(n, z, N.predecessor(n, w))) == Cmp.is_lt(Word.cmp(n, z, w)) : Bool}
def compare_combined_predecessor_positive(n, z, w, negative_zero):
  Equal.trans(Bool, Cmp.is_le(Word.cmp(n, z, N.predecessor(n, w))), Cmp.is_lt(Word.cmp(n, z, Word.inc(n, N.predecessor(n, w)))), Cmp.is_lt(Word.cmp(n, z, w)),
    U.word_limit_successor(n, z, N.predecessor(n, w), predecessor_positive_can_be_incremented(n, w, negative_zero)),
    Equal.cong(Word(n), Bool, r => Cmp.is_lt(Word.cmp(n, z, r)), Word.inc(n, N.predecessor(n, w)), w, N.increment_of_predecessor(n, w)))

law predecessor_positive_and_strictly_less:
  for +n: Nat
  for +w: Word(n)
  for negative_zero: {N.zeros(n, w) == False{} : Bool}
  {Cmp.is_lt(Word.cmp(n, N.predecessor(n, w), w)) == True{} : Bool}
def predecessor_positive_and_strictly_less(n, w, negative_zero):
  Equal.trans(Bool, Cmp.is_lt(Word.cmp(n, N.predecessor(n, w), w)), Cmp.is_le(Word.cmp(n, N.predecessor(n, w), N.predecessor(n, w))), True{},
    Equal.sym(Bool, Cmp.is_le(Word.cmp(n, N.predecessor(n, w), N.predecessor(n, w))), Cmp.is_lt(Word.cmp(n, N.predecessor(n, w), w)),
      compare_combined_predecessor_positive(n, N.predecessor(n, w), w, negative_zero)),
    Equal.cong(Cmp, Bool, c => Cmp.is_le(c), Word.cmp(n, N.predecessor(n, w), N.predecessor(n, w)), EQ{}, O.word_refl(n, N.predecessor(n, w))))

# LT/READS transitivity, including equality at the limit.
def coherence_lt_reads(bc: Cmp, -ac: Cmp, coherent: O.Coherent(LT{}, bc, ac),
  reads: {Cmp.is_le(bc) == True{} : Bool}) -> {ac == LT{} : Cmp}:
  match bc:
    case EQ{}:
      coherent
    case LT{}:
      coherent
    case GT{}:
      F.absurd_boolean({ac == LT{} : Cmp}, reads)

law word_lt_reads_transitive:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +c: Word(n)
  for ab: {Cmp.is_lt(Word.cmp(n, a, b)) == True{} : Bool}
  for bc: {Cmp.is_le(Word.cmp(n, b, c)) == True{} : Bool}
  {Cmp.is_lt(Word.cmp(n, a, c)) == True{} : Bool}
def word_lt_reads_transitive(n, a, b, c, ab, bc):
  h = {(%O.cmp_lt(Word.cmp(n, a, b), ab) : O.Coherent(_, Word.cmp(n, b, c), Word.cmp(n, a, c))
    O.word_coherent(n, a, b, c)) : O.Coherent(LT{}, Word.cmp(n, b, c), Word.cmp(n, a, c))}
  Equal.cong(Cmp, Bool, k => Cmp.is_lt(k), Word.cmp(n, a, c), LT{}, coherence_lt_reads(Word.cmp(n, b, c), Word.cmp(n, a, c), h, bc))

law predecessor_preserves_order_positive:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for reads: {Cmp.is_le(Word.cmp(n, a, b)) == True{} : Bool}
  for positive_to: {N.zeros(n, a) == False{} : Bool}
  for positive_b: {N.zeros(n, b) == False{} : Bool}
  {Cmp.is_le(Word.cmp(n, N.predecessor(n, a), N.predecessor(n, b))) == True{} : Bool}
def predecessor_preserves_order_positive(n, a, b, reads, positive_to, positive_b):
  Equal.trans(Bool, Cmp.is_le(Word.cmp(n, N.predecessor(n, a), N.predecessor(n, b))), Cmp.is_lt(Word.cmp(n, N.predecessor(n, a), b)), True{},
    compare_combined_predecessor_positive(n, N.predecessor(n, a), b, positive_b),
    word_lt_reads_transitive(n, N.predecessor(n, a), a, b, predecessor_positive_and_strictly_less(n, a, positive_to), reads))

law and_boolean_commutes:
  for a: Bool
  for b: Bool
  {a && b == b && a : Bool}
def and_boolean_commutes(a, b):
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

law zeros_of_blocks:
  for +k: Nat
  for +n: Nat
  for +lo: Word(k)
  for +hi: Word(n)
  {N.zeros(Nat.add(k, n), W.join(k, n, lo, hi)) == N.zeros(k, lo) && N.zeros(n, hi) : Bool}
def zeros_of_blocks(k, n, lo, hi):
  match k:
    case 0n:
      {==}
    case 1n+p:
      match lo:
        case WCon{False{}, t}:
          zeros_of_blocks(p, n, t, hi)
        case WCon{True{}, t}:
          {==}

def bits64(q: B.Number64) -> Word(64n):
  B.Number64{a, b} = q
  W.join(32n, 32n, H.bits(b), H.bits(a))

law zero64_equivalent_bits_zero:
  for +q: B.Number64
  {C.zero64(q) == N.zeros(64n, bits64(q)) : Bool}
def zero64_equivalent_bits_zero(q):
  match q:
    case B.Number64{U32{+a}, U32{+b}}:
      %Equal.sym(Bool, Cmp.is_eq(Word.cmp(32n, a, Word.zero(32n))), N.zeros(32n, a), N.comparison_zero_recognizes_bits(32n, a)) :
        {_ && Cmp.is_eq(Word.cmp(32n, b, Word.zero(32n))) == N.zeros(64n, W.join(32n, 32n, b, a)) : Bool}
      %Equal.sym(Bool, Cmp.is_eq(Word.cmp(32n, b, Word.zero(32n))), N.zeros(32n, b), N.comparison_zero_recognizes_bits(32n, b)) :
        {N.zeros(32n, a) && _ == N.zeros(64n, W.join(32n, 32n, b, a)) : Bool}
      Equal.trans(Bool, N.zeros(32n, a) && N.zeros(32n, b), N.zeros(32n, b) && N.zeros(32n, a), N.zeros(64n, W.join(32n, 32n, b, a)),
        and_boolean_commutes(N.zeros(32n, a), N.zeros(32n, b)),
        Equal.sym(Bool, N.zeros(64n, W.join(32n, 32n, b, a)), N.zeros(32n, b) && N.zeros(32n, a), zeros_of_blocks(32n, 32n, b, a)))

law predecessor_block_low_positive:
  for +k: Nat
  for +n: Nat
  for +lo: Word(k)
  for +hi: Word(n)
  for positive: {N.zeros(k, lo) == False{} : Bool}
  {N.predecessor(Nat.add(k, n), W.join(k, n, lo, hi)) == W.join(k, n, N.predecessor(k, lo), hi) : Word(Nat.add(k, n))}
def predecessor_block_low_positive(k, n, lo, hi, positive):
  match k:
    case 0n:
      F.absurd_boolean({N.predecessor(n, W.join(0n, n, lo, hi)) == W.join(0n, n, N.predecessor(0n, lo), hi) : Word(n)}, Equal.sym(Bool, True{}, False{}, positive))
    case 1n+p:
      match lo:
        case WCon{True{}, t}:
          {==}
        case WCon{False{}, +t}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), r => WCon{True{}, r},
            N.predecessor(Nat.add(p, n), W.join(p, n, t, hi)), W.join(p, n, N.predecessor(p, t), hi),
            predecessor_block_low_positive(p, n, t, hi, positive))

law predecessor_block_low_zero:
  for +k: Nat
  for +n: Nat
  for +hi: Word(n)
  {N.predecessor(Nat.add(k, n), W.zeros_low(k, n, hi)) == W.join(k, n, W.ones(k), N.predecessor(n, hi)) : Word(Nat.add(k, n))}
def predecessor_block_low_zero(k, n, hi):
  match k:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), r => WCon{True{}, r},
        N.predecessor(Nat.add(p, n), W.zeros_low(p, n, hi)), W.join(p, n, W.ones(p), N.predecessor(n, hi)), predecessor_block_low_zero(p, n, hi))

def decrease_bits_without_transport(+a: U32, +b: U32,
  negative_zero: {U32.is_eq(b, 0) == False{} : Bool}) ->
  {bits64(B.Number64{a, (b - 1 : U32)}) == N.predecessor(64n, bits64(B.Number64{a, b})) : Word(64n)}:
  match a b:
    case U32{+hi} U32{+lo}:
      %Equal.sym(Word(32n), Word.sub(32n, lo, N.one(31n)), N.predecessor(32n, lo), N.subtract_one_decrements(31n, lo)) :
        {W.join(32n, 32n, _, hi) == N.predecessor(64n, W.join(32n, 32n, lo, hi)) : Word(64n)}
      Equal.sym(Word(64n), N.predecessor(64n, W.join(32n, 32n, lo, hi)), W.join(32n, 32n, N.predecessor(32n, lo), hi),
        predecessor_block_low_positive(32n, 32n, lo, hi,
          Equal.trans(Bool, N.zeros(32n, lo), Cmp.is_eq(Word.cmp(32n, lo, Word.zero(32n))), False{},
            Equal.sym(Bool, Cmp.is_eq(Word.cmp(32n, lo, Word.zero(32n))), N.zeros(32n, lo), N.comparison_zero_recognizes_bits(32n, lo)), negative_zero)))

def decrease_bits_combined_transport(+a: U32) ->
  {bits64(B.Number64{(a - 1 : U32), 4294967295}) == N.predecessor(64n, bits64(B.Number64{a, 0})) : Word(64n)}:
  match a:
    case U32{+hi}:
      %Equal.sym(Word(32n), Word.sub(32n, hi, N.one(31n)), N.predecessor(32n, hi), N.subtract_one_decrements(31n, hi)) :
        {W.join(32n, 32n, W.ones(32n), _) == N.predecessor(64n, W.join(32n, 32n, Word.zero(32n), hi)) : Word(64n)}
      Equal.sym(Word(64n), N.predecessor(64n, W.zeros_low(32n, 32n, hi)), W.join(32n, 32n, W.ones(32n), N.predecessor(32n, hi)), predecessor_block_low_zero(32n, 32n, hi))

def decrease_bits_cases(low_zero: Bool, high_zero: Bool, +a: U32, +b: U32,
  eb: {U32.is_eq(b, 0) == low_zero : Bool},
  ea: {U32.is_eq(a, 0) == high_zero : Bool},
  positive: {high_zero && low_zero == False{} : Bool}) ->
  {bits64(C.decrease64_cases(low_zero, high_zero, a, b)) == N.predecessor(64n, bits64(B.Number64{a, b})) : Word(64n)}:
  match low_zero high_zero:
    case False{} _:
      decrease_bits_without_transport(a, b, eb)
    case True{} False{}:
      %Equal.sym(U32, b, 0, N.equality_u32(b, 0, eb)) :
        {bits64(B.Number64{(a - 1 : U32), 4294967295}) == N.predecessor(64n, bits64(B.Number64{a, _})) : Word(64n)}
      decrease_bits_combined_transport(a)
    case True{} True{}:
      F.absurd_boolean({bits64(B.Number64{0, 0}) == N.predecessor(64n, bits64(B.Number64{a, b})) : Word(64n)}, Equal.sym(Bool, True{}, False{}, positive))


law decrease64_represents_predecessor_positive:
  for +q: B.Number64
  for positive: {C.zero64(q) == False{} : Bool}
  {bits64(C.decrease64(q)) == N.predecessor(64n, bits64(q)) : Word(64n)}
def decrease64_represents_predecessor_positive(q, positive):
  match q:
    case B.Number64{+a, +b}:
      decrease_bits_cases(U32.is_eq(b, 0), U32.is_eq(a, 0), a, b, {==}, {==}, positive)

law comparison_lexicographic:
  for a: Cmp
  for b: Cmp
  {Cmp.is_lt(a) || (Cmp.is_eq(a) && Cmp.is_le(b)) == Cmp.is_le(O.priority(a, b)) : Bool}
def comparison_lexicographic(a, b):
  match a:
    case EQ{}:
      {==}
    case LT{}:
      {==}
    case GT{}:
      {==}

law less_equal64_equivalent_order_of_bits:
  for +a: B.Number64
  for +b: B.Number64
  {C.less_equal64(a, b) == Cmp.is_le(Word.cmp(64n, bits64(a), bits64(b))) : Bool}
def less_equal64_equivalent_order_of_bits(a, b):
  match a b:
    case B.Number64{U32{+ah}, U32{+al}} B.Number64{U32{+bh}, U32{+bl}}:
      Equal.trans(Bool, Cmp.is_lt(Word.cmp(32n, ah, bh)) || (Cmp.is_eq(Word.cmp(32n, ah, bh)) && Cmp.is_le(Word.cmp(32n, al, bl))),
        Cmp.is_le(O.priority(Word.cmp(32n, ah, bh), Word.cmp(32n, al, bl))), Cmp.is_le(Word.cmp(64n, W.join(32n, 32n, al, ah), W.join(32n, 32n, bl, bh))),
        comparison_lexicographic(Word.cmp(32n, ah, bh), Word.cmp(32n, al, bl)),
        Equal.cong(Cmp, Bool, c => Cmp.is_le(c), O.priority(Word.cmp(32n, ah, bh), Word.cmp(32n, al, bl)), Word.cmp(64n, W.join(32n, 32n, al, ah), W.join(32n, 32n, bl, bh)),
          Equal.sym(Cmp, Word.cmp(64n, W.join(32n, 32n, al, ah), W.join(32n, 32n, bl, bh)), O.priority(Word.cmp(32n, ah, bh), Word.cmp(32n, al, bl)), A.compare_blocks(32n, 32n, al, bl, ah, bh))))

law cmp_zero_bit_negative_greater:
  for b: Bool
  for c: Cmp
  for e: {Cmp.is_le(c) == True{} : Bool}
  {Cmp.is_le(Word.cmp.fin(False{}, b, c)) == True{} : Bool}
def cmp_zero_bit_negative_greater(b, c, e):
  match b c:
    case False{} EQ{}:
      {==}
    case True{} EQ{}:
      {==}
    case False{} LT{}:
      {==}
    case True{} LT{}:
      {==}
    case False{} GT{}:
      F.absurd_boolean({False{} == True{} : Bool}, e)
    case True{} GT{}:
      F.absurd_boolean({False{} == True{} : Bool}, e)

law word_zero_negative_greater:
  for +n: Nat
  for +w: Word(n)
  {Cmp.is_le(Word.cmp(n, Word.zero(n), w)) == True{} : Bool}
def word_zero_negative_greater(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, +t}:
          cmp_zero_bit_negative_greater(b, Word.cmp(p, Word.zero(p), t), word_zero_negative_greater(p, t))

law zero64_negative_greater:
  for +q: B.Number64
  {C.less_equal64(B.Number64{0, 0}, q) == True{} : Bool}
def zero64_negative_greater(q):
  Equal.trans(Bool, C.less_equal64(B.Number64{0, 0}, q), Cmp.is_le(Word.cmp(64n, Word.zero(64n), bits64(q))), True{},
    less_equal64_equivalent_order_of_bits(B.Number64{0, 0}, q), word_zero_negative_greater(64n, bits64(q)))

law less_equal_to_zero64_and_zero:
  for +q: B.Number64
  for reads: {C.less_equal64(q, B.Number64{0, 0}) == True{} : Bool}
  {C.zero64(q) == True{} : Bool}
def less_equal_to_zero64_and_zero(q, reads):
  bounded = Equal.trans(Bool, Cmp.is_le(Word.cmp(64n, bits64(q), Word.zero(64n))), C.less_equal64(q, B.Number64{0, 0}), True{},
    Equal.sym(Bool, C.less_equal64(q, B.Number64{0, 0}), Cmp.is_le(Word.cmp(64n, bits64(q), Word.zero(64n))), less_equal64_equivalent_order_of_bits(q, B.Number64{0, 0})), reads)
  Equal.trans(Bool, C.zero64(q), N.zeros(64n, bits64(q)), True{}, zero64_equivalent_bits_zero(q),
    Equal.cong(Word(64n), Bool, w => N.zeros(64n, w), bits64(q), Word.zero(64n), W.word_until_zero(64n, bits64(q), bounded)))

law limit_of_positive_and_positive:
  for +a: B.Number64
  for +b: B.Number64
  for reads: {C.less_equal64(a, b) == True{} : Bool}
  for positive: {C.zero64(a) == False{} : Bool}
  {C.zero64(b) == False{} : Bool}
def limit_of_positive_and_positive(a, b, reads, positive):
  N.false_se_true_impossible(C.zero64(b), e =>
    F.false_negative_true(Equal.trans(Bool, False{}, C.zero64(a), True{}, Equal.sym(Bool, C.zero64(a), False{}, positive),
      less_equal_to_zero64_and_zero(a,
        (%N.zero64_only_recognizes_zero(b, e) : {C.less_equal64(a, _) == True{} : Bool}
          reads)))))

def decrease_limits_cases(zero_to: Bool, +a: B.Number64, +b: B.Number64,
  +ea: {C.zero64(a) == zero_to : Bool}, +reads: {C.less_equal64(a, b) == True{} : Bool}) ->
  {C.less_equal64(C.decrease64(a), C.decrease64(b)) == True{} : Bool}:
  match zero_to:
    case True{}:
      %Equal.sym(B.Number64, a, B.Number64{0, 0}, N.zero64_only_recognizes_zero(a, ea)) :
        {C.less_equal64(C.decrease64(_), C.decrease64(b)) == True{} : Bool}
      zero64_negative_greater(C.decrease64(b))
    case False{}:
      +positive_b = limit_of_positive_and_positive(a, b, reads, ea)
      order = Equal.trans(Bool, Cmp.is_le(Word.cmp(64n, bits64(a), bits64(b))), C.less_equal64(a, b), True{},
        Equal.sym(Bool, C.less_equal64(a, b), Cmp.is_le(Word.cmp(64n, bits64(a), bits64(b))), less_equal64_equivalent_order_of_bits(a, b)), reads)
      zeros_to = Equal.trans(Bool, N.zeros(64n, bits64(a)), C.zero64(a), False{}, Equal.sym(Bool, C.zero64(a), N.zeros(64n, bits64(a)), zero64_equivalent_bits_zero(a)), ea)
      zeros_b = Equal.trans(Bool, N.zeros(64n, bits64(b)), C.zero64(b), False{}, Equal.sym(Bool, C.zero64(b), N.zeros(64n, bits64(b)), zero64_equivalent_bits_zero(b)), positive_b)
      Equal.trans(Bool, C.less_equal64(C.decrease64(a), C.decrease64(b)), Cmp.is_le(Word.cmp(64n, bits64(C.decrease64(a)), bits64(C.decrease64(b)))), True{},
        less_equal64_equivalent_order_of_bits(C.decrease64(a), C.decrease64(b)),
        (%Equal.sym(Word(64n), bits64(C.decrease64(a)), N.predecessor(64n, bits64(a)), decrease64_represents_predecessor_positive(a, ea)) :
          {Cmp.is_le(Word.cmp(64n, _, bits64(C.decrease64(b)))) == True{} : Bool}
          %Equal.sym(Word(64n), bits64(C.decrease64(b)), N.predecessor(64n, bits64(b)), decrease64_represents_predecessor_positive(b, positive_b)) :
            {Cmp.is_le(Word.cmp(64n, N.predecessor(64n, bits64(a)), _)) == True{} : Bool}
          predecessor_preserves_order_positive(64n, bits64(a), bits64(b), order, zeros_to, zeros_b)))

law decrease64_preserves_order_of_limits:
  for +a: B.Number64
  for +b: B.Number64
  for reads: {C.less_equal64(a, b) == True{} : Bool}
  {C.less_equal64(C.decrease64(a), C.decrease64(b)) == True{} : Bool}
def decrease64_preserves_order_of_limits(a, b, reads):
  decrease_limits_cases(C.zero64(a), a, b, {==}, reads)

law decrease_repeated_preserves_order_of_limits:
  for +n: Nat
  for +a: B.Number64
  for +b: B.Number64
  for reads: {C.less_equal64(a, b) == True{} : Bool}
  {C.less_equal64(H.decrease(n, a), H.decrease(n, b)) == True{} : Bool}
def decrease_repeated_preserves_order_of_limits(n, a, b, reads):
  match n:
    case 0n:
      reads
    case 1n+p:
      decrease64_preserves_order_of_limits(H.decrease(p, a), H.decrease(p, b), decrease_repeated_preserves_order_of_limits(p, a, b, reads))

def ceiling_frame(q: R.Frame) -> B.Number64:
  R.Frame{body, ceiling, m} = q
  ceiling

law any_prefix_preserves_body_inside_of_ceiling:
  for bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for +m: C.Machine
  for reads: {C.less_equal64(body, ceiling) == True{} : Bool}
  {C.less_equal64(N.body_frame(R.execute(bs, R.Frame{body, ceiling, m})), ceiling_frame(R.execute(bs, R.Frame{body, ceiling, m}))) == True{} : Bool}
def any_prefix_preserves_body_inside_of_ceiling(bs, body, ceiling, m, reads):
  match bs:
    case Nil{}:
      reads
    case Con{+b, t}:
      +rest = C.decrease64(body)
      +free = C.decrease64(ceiling)
      any_prefix_preserves_body_inside_of_ceiling(t, rest, free, C.step(m, b, rest, free), decrease64_preserves_order_of_limits(body, ceiling, reads))
