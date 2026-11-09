# A strict remainder below a divisor of magnitude at most 2^63 has a clear
# high bit. The proof uses exact binary order, never unary radix comparisons.
import Base
import ./Int64Flags.bend as G
import ./Int64Proofs.bend as A
import ./Int64.bend as I
import ./Value.bend as V
import ../proof/Orders.bend as O
import ../proof/Foundations.bend as F

law strict_then_weak_is_strict:
  for +ab: Cmp
  for +bc: Cmp
  for +ac: Cmp
  for first: {Cmp.is_lt(ab) == True{} : Bool}
  for second: {Cmp.is_le(bc) == True{} : Bool}
  for order: O.Coherent(ab,bc,ac)
  {ac == LT{} : Cmp}
def strict_then_weak_is_strict(ab,bc,ac,first,second,order):
  match ab bc:
    case LT{} LT{}: order
    case LT{} EQ{}: order
    case LT{} GT{}: F.absurd_boolean({ac == LT{} : Cmp},second)
    case EQ{} _: F.absurd_boolean({ac == LT{} : Cmp},first)
    case GT{} _: F.absurd_boolean({ac == LT{} : Cmp},first)

law below_threshold_clears_top:
  for +n: Nat
  for +r: Word(1n+n)
  for +d: Word(1n+n)
  for small: {Cmp.is_lt(Word.cmp(1n+n,r,d)) == True{} : Bool}
  for bound: {Cmp.is_le(Word.cmp(1n+n,d,A.sign_threshold(n))) == True{} : Bool}
  {A.top(1n+n,r) == False{} : Bool}
def below_threshold_clears_top(n,r,d,small,bound):
  Equal.trans(Bool,A.top(1n+n,r),Cmp.is_ge(Word.cmp(1n+n,r,A.sign_threshold(n))),False{},
    Equal.sym(Bool,Cmp.is_ge(Word.cmp(1n+n,r,A.sign_threshold(n))),A.top(1n+n,r),A.sign_threshold_is_top(n,r)),
    Equal.cong(Cmp,Bool,Cmp.is_ge,Word.cmp(1n+n,r,A.sign_threshold(n)),LT{},
      strict_then_weak_is_strict(Word.cmp(1n+n,r,d),Word.cmp(1n+n,d,A.sign_threshold(n)),Word.cmp(1n+n,r,A.sign_threshold(n)),small,bound,O.word_coherent(1n+n,r,d,A.sign_threshold(n)))))

law remainder_high_bit_is_clear:
  for +r: V.Int64
  for +d: V.Int64
  for small: {I.unsigned_lt(r,d) == True{} : Bool}
  for bound: {Cmp.is_le(Word.cmp(64n,A.bits(d),A.sign_threshold(63n))) == True{} : Bool}
  {I.negative(r) == False{} : Bool}
def remainder_high_bit_is_clear(r,d,small,bound):
  Equal.trans(Bool,I.negative(r),A.top(64n,A.bits(r)),False{},A.negative_is_sign_bit(r),
    below_threshold_clears_top(63n,A.bits(r),A.bits(d),Equal.trans(Bool,Cmp.is_lt(Word.cmp(64n,A.bits(r),A.bits(d))),I.unsigned_lt(r,d),True{},
      Equal.sym(Bool,I.unsigned_lt(r,d),Cmp.is_lt(Word.cmp(64n,A.bits(r),A.bits(d))),G.unsigned_lt_is_word_order(r,d)),small),bound))
