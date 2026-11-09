# Unsigned absolute magnitude is independent of signed overflow conversion.
# In particular abs(INT64_MIN) is retained as the unsigned word 2^63.
import Base
import ../contract/Logic.bend as L
import ./Value.bend as V
import ./Int64.bend as I
import ./Int64Proofs.bend as A
import ./Int64Subtraction.bend as Sub
import ../proof/Orders.bend as O
import ../proof/Foundations.bend as F
import ../proof/CodecSumsBits.bend as S
import ./Int64Flags.bend as G
import ./Int64RangeBits.bend as Bits

def IntegerEqual(a: A.Integer, b: A.Integer) -> Type:
  A.Integer{ap, an} = a
  A.Integer{bp, bn} = b
  {Nat.add(ap, bn) == Nat.add(bp, an) : Nat}

def sign_integer(negative: Bool, value: Nat) -> A.Integer:
  match negative:
    case False{}: A.Integer{value, 0n}
    case True{}: A.Integer{0n, value}

law integer_uses_actual_sign:
  for +x: V.Int64
  {A.integer(x) == A.Integer{A.unsigned(x), A.spill(64n, I.negative(x))} : A.Integer}
def integer_uses_actual_sign(x):
  Equal.cong(Bool, A.Integer, sign => A.Integer{A.unsigned(x), A.spill(64n, sign)}, A.top(64n, A.bits(x)), I.negative(x),
    Equal.sym(Bool, I.negative(x), A.top(64n, A.bits(x)), A.negative_is_sign_bit(x)))

law lt_cmp_is_literal:
  for c: Cmp
  for true: {Cmp.is_lt(c) == True{} : Bool}
  {c == LT{} : Cmp}
def lt_cmp_is_literal(c, true):
  match c:
    case LT{}: {==}
    case EQ{}: F.absurd_boolean({EQ{} == LT{} : Cmp}, true)
    case GT{}: F.absurd_boolean({GT{} == LT{} : Cmp}, true)

law top_set_word_exceeds_zero:
  for +n: Nat
  for +w: Word(1n+n)
  for top: {A.top(1n+n, w) == True{} : Bool}
  {Cmp.is_lt(Word.cmp(1n+n, Word.zero(1n+n), w)) == True{} : Bool}
def top_set_word_exceeds_zero(n, w, top):
  match n:
    case 0n:
      match w:
        case WCon{False{}, WNil{}}: top
        case WCon{True{}, WNil{}}: {==}
    case 1n+p:
      match w:
        case WCon{b, +tail}:
          %Equal.sym(Cmp, Word.cmp(1n+p, Word.zero(1n+p), tail), LT{},
            lt_cmp_is_literal(Word.cmp(1n+p, Word.zero(1n+p), tail), top_set_word_exceeds_zero(p, tail, top))) :
            {Cmp.is_lt(Word.cmp.fin(False{}, b, _)) == True{} : Bool}
          {==}

law negative_word_exceeds_unsigned_zero:
  for +x: V.Int64
  for negative: {I.negative(x) == True{} : Bool}
  {I.unsigned_lt(V.Int64{0, 0}, x) == True{} : Bool}
def negative_word_exceeds_unsigned_zero(x, negative):
  Equal.trans(Bool, I.unsigned_lt(V.Int64{0, 0}, x), Cmp.is_lt(Word.cmp(64n, Word.zero(64n), A.bits(x))), True{},
    G.unsigned_lt_is_word_order(V.Int64{0, 0}, x), top_set_word_exceeds_zero(63n, A.bits(x),
      Equal.trans(Bool, A.top(64n, A.bits(x)), I.negative(x), True{},
        Equal.sym(Bool, I.negative(x), A.top(64n, A.bits(x)), A.negative_is_sign_bit(x)), negative)))

