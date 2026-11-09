# Bit-level range characterization, with no natural 2^63 normalization.
import Base
import ./Int64Proofs.bend as A
import ./Int64SubProofs.bend as Sub
import ./Int64.bend as I
import ./Value.bend as V
import ./ComparisonProofs.bend as C
import ../proof/Orders.bend as O
import ../proof/Foundations.bend as F
import ./Int64Flags.bend as G

law zero_minus_without_incoming_carry_is_complement:
  for +n: Nat
  for +w: Word(n)
  {Word.adc(n, Word.zero(n), w, True{}, False{}) == Word.not(n, w) : Word(n)}
def zero_minus_without_incoming_carry_is_complement(n, w):
  match n:
    case 0n: {==}
    case 1n+p:
      match w:
        case WCon{False{}, +tail}:
          Equal.cong(Word(p), Word(1n+p), t => WCon{True{}, t}, Word.adc(p, Word.zero(p), tail, True{}, False{}), Word.not(p, tail),
            zero_minus_without_incoming_carry_is_complement(p, tail))
        case WCon{True{}, +tail}:
          Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t}, Word.adc(p, Word.zero(p), tail, True{}, False{}), Word.not(p, tail),
            zero_minus_without_incoming_carry_is_complement(p, tail))

law top_of_nonempty_complement:
  for +n: Nat
  for +w: Word(1n+n)
  {A.top(1n+n, Word.not(1n+n, w)) == Bool.not(A.top(1n+n, w)) : Bool}
def top_of_nonempty_complement(n, w):
  match n:
    case 0n:
      match w:
        case WCon{b, WNil{}}: {==}
    case 1n+p:
      match w:
        case WCon{b, +tail}: top_of_nonempty_complement(p, tail)

law reversed_word_comparison:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Word.cmp(n, b, a) == C.reverse_cmp(Word.cmp(n, a, b)) : Cmp}
def reversed_word_comparison(n, a, b):
  C.coherent_inverse(Word.cmp(n, a, b), Word.cmp(n, b, a),
    (%O.word_refl(n, a) : O.Coherent(Word.cmp(n, a, b), Word.cmp(n, b, a), _)
      O.word_coherent(n, a, b, a)))

law reversed_le_is_ge:
  for c: Cmp
  {Cmp.is_le(C.reverse_cmp(c)) == Cmp.is_ge(c) : Bool}
def reversed_le_is_ge(c):
  match c:
    case LT{}: {==}
    case EQ{}: {==}
    case GT{}: {==}

law low_bit_extends_equal_threshold:
  for c: Cmp
  {Cmp.is_lt(Word.cmp.fin(False{}, True{}, c)) == Cmp.is_le(c) : Bool}
def low_bit_extends_equal_threshold(c):
  match c:
    case LT{}: {==}
    case EQ{}: {==}
    case GT{}: {==}

law threshold_is_at_most_iff_top:
  for +n: Nat
  for +w: Word(1n+n)
  {Cmp.is_le(Word.cmp(1n+n, A.sign_threshold(n), w)) == A.top(1n+n, w) : Bool}
def threshold_is_at_most_iff_top(n, w):
  Equal.trans(Bool, Cmp.is_le(Word.cmp(1n+n, A.sign_threshold(n), w)),
    Cmp.is_le(C.reverse_cmp(Word.cmp(1n+n, w, A.sign_threshold(n)))), A.top(1n+n, w),
    Equal.cong(Cmp, Bool, Cmp.is_le, Word.cmp(1n+n, A.sign_threshold(n), w), C.reverse_cmp(Word.cmp(1n+n, w, A.sign_threshold(n))),
      reversed_word_comparison(1n+n, w, A.sign_threshold(n))),
    Equal.trans(Bool, Cmp.is_le(C.reverse_cmp(Word.cmp(1n+n, w, A.sign_threshold(n)))),
      Cmp.is_ge(Word.cmp(1n+n, w, A.sign_threshold(n))), A.top(1n+n, w),
      reversed_le_is_ge(Word.cmp(1n+n, w, A.sign_threshold(n))), A.sign_threshold_is_top(n, w)))

law boolean_sign_reduction:
  for b: Bool
  {b && Bool.not(Bool.not(b)) == b : Bool}
def boolean_sign_reduction(b):
  match b:
    case False{}: {==}
    case True{}: {==}

law equal_zero_low_bit_preserves_comparison:
  for c: Cmp
  {Word.cmp.fin(False{}, False{}, c) == c : Cmp}
def equal_zero_low_bit_preserves_comparison(c):
  match c:
    case LT{}: {==}
    case EQ{}: {==}
    case GT{}: {==}

law unsigned_above_minimum_is_sign_without_negative_opposite:
  for +n: Nat
  for +w: Word(1n+n)
  {Cmp.is_lt(Word.cmp(1n+n, A.sign_threshold(n), w)) ==
    (A.top(1n+n, w) && Bool.not(A.top(1n+n, Word.sub(1n+n, Word.zero(1n+n), w)))) : Bool}
def unsigned_above_minimum_is_sign_without_negative_opposite(n, w):
  match n:
    case 0n:
      match w:
        case WCon{False{}, WNil{}}: {==}
        case WCon{True{}, WNil{}}: {==}
    case 1n+p:
      match w:
        case WCon{False{}, +tail}:
          Equal.trans(Bool, Cmp.is_lt(Word.cmp.fin(False{}, False{}, Word.cmp(1n+p, A.sign_threshold(p), tail))),
            Cmp.is_lt(Word.cmp(1n+p, A.sign_threshold(p), tail)),
            A.top(1n+p, tail) && Bool.not(A.top(1n+p, Word.sub(1n+p, Word.zero(1n+p), tail))),
            Equal.cong(Cmp, Bool, Cmp.is_lt, Word.cmp.fin(False{}, False{}, Word.cmp(1n+p, A.sign_threshold(p), tail)),
              Word.cmp(1n+p, A.sign_threshold(p), tail), equal_zero_low_bit_preserves_comparison(Word.cmp(1n+p, A.sign_threshold(p), tail))),
            unsigned_above_minimum_is_sign_without_negative_opposite(p, tail))
        case WCon{True{}, +tail}:
          Equal.trans(Bool, Cmp.is_lt(Word.cmp.fin(False{}, True{}, Word.cmp(1n+p, A.sign_threshold(p), tail))),
            Cmp.is_le(Word.cmp(1n+p, A.sign_threshold(p), tail)),
            A.top(1n+p, tail) && Bool.not(A.top(1n+p, Word.adc(1n+p, Word.zero(1n+p), tail, True{}, False{}))),
            low_bit_extends_equal_threshold(Word.cmp(1n+p, A.sign_threshold(p), tail)),
            Equal.trans(Bool, Cmp.is_le(Word.cmp(1n+p, A.sign_threshold(p), tail)), A.top(1n+p, tail),
              A.top(1n+p, tail) && Bool.not(A.top(1n+p, Word.adc(1n+p, Word.zero(1n+p), tail, True{}, False{}))),
              threshold_is_at_most_iff_top(p, tail),
              Equal.trans(Bool, A.top(1n+p, tail), A.top(1n+p, tail) && Bool.not(Bool.not(A.top(1n+p, tail))),
                A.top(1n+p, tail) && Bool.not(A.top(1n+p, Word.adc(1n+p, Word.zero(1n+p), tail, True{}, False{}))),
                Equal.sym(Bool, A.top(1n+p, tail) && Bool.not(Bool.not(A.top(1n+p, tail))), A.top(1n+p, tail), boolean_sign_reduction(A.top(1n+p, tail))),
                Equal.cong(Bool, Bool, b => A.top(1n+p, tail) && Bool.not(b), Bool.not(A.top(1n+p, tail)),
                  A.top(1n+p, Word.adc(1n+p, Word.zero(1n+p), tail, True{}, False{})),
                  Equal.sym(Bool, A.top(1n+p, Word.adc(1n+p, Word.zero(1n+p), tail, True{}, False{})), Bool.not(A.top(1n+p, tail)),
                    Equal.trans(Bool, A.top(1n+p, Word.adc(1n+p, Word.zero(1n+p), tail, True{}, False{})),
                      A.top(1n+p, Word.not(1n+p, tail)), Bool.not(A.top(1n+p, tail)),
                      Equal.cong(Word(1n+p), Bool, bits => A.top(1n+p, bits), Word.adc(1n+p, Word.zero(1n+p), tail, True{}, False{}), Word.not(1n+p, tail),
                        zero_minus_without_incoming_carry_is_complement(1n+p, tail)),
                      top_of_nonempty_complement(p, tail)))))))

def opposite(x: V.Int64) -> V.Int64:
  I.wrapping_sub(V.Int64{0, 0}, x)

law actual_negative_range_is_exact_opposite_sign_guard:
  for +x: V.Int64
  {I.out_of_range(True{}, x) == (I.negative(x) && Bool.not(I.negative(opposite(x)))) : Bool}
def actual_negative_range_is_exact_opposite_sign_guard(x):
  Equal.trans(Bool, I.out_of_range(True{}, x), Cmp.is_lt(Word.cmp(64n, A.sign_threshold(63n), A.bits(x))),
    I.negative(x) && Bool.not(I.negative(opposite(x))), G.unsigned_lt_is_word_order(V.Int64{2147483648, 0}, x),
    Equal.trans(Bool, Cmp.is_lt(Word.cmp(64n, A.sign_threshold(63n), A.bits(x))),
      A.top(64n, A.bits(x)) && Bool.not(A.top(64n, Word.sub(64n, Word.zero(64n), A.bits(x)))),
      I.negative(x) && Bool.not(I.negative(opposite(x))), unsigned_above_minimum_is_sign_without_negative_opposite(63n, A.bits(x)),
      Equal.trans(Bool, A.top(64n, A.bits(x)) && Bool.not(A.top(64n, Word.sub(64n, Word.zero(64n), A.bits(x)))),
        I.negative(x) && Bool.not(A.top(64n, Word.sub(64n, Word.zero(64n), A.bits(x)))), I.negative(x) && Bool.not(I.negative(opposite(x))),
        Equal.cong(Bool, Bool, b => b && Bool.not(A.top(64n, Word.sub(64n, Word.zero(64n), A.bits(x)))),
          A.top(64n, A.bits(x)), I.negative(x), Equal.sym(Bool, I.negative(x), A.top(64n, A.bits(x)), A.negative_is_sign_bit(x))),
        Equal.cong(Bool, Bool, b => I.negative(x) && Bool.not(b), A.top(64n, Word.sub(64n, Word.zero(64n), A.bits(x))), I.negative(opposite(x)),
          Equal.trans(Bool, A.top(64n, Word.sub(64n, Word.zero(64n), A.bits(x))), A.top(64n, A.bits(opposite(x))), I.negative(opposite(x)),
            Equal.cong(Word(64n), Bool, w => A.top(64n, w), Word.sub(64n, Word.zero(64n), A.bits(x)), A.bits(opposite(x)),
              Equal.sym(Word(64n), A.bits(opposite(x)), Word.sub(64n, Word.zero(64n), A.bits(x)), Sub.wrapping_sub_is_full_word_sub(V.Int64{0, 0}, x))),
            Equal.sym(Bool, I.negative(opposite(x)), A.top(64n, A.bits(opposite(x))), A.negative_is_sign_bit(opposite(x))))))))
