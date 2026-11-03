# General lemmas about scalars ACTUALLY emitted by the parser.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./Orders.bend as O

# A Word increment is used below only when a zero bit exists.
def without_transport(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          True{}
        case WCon{True{}, t}:
          without_transport(p, t)

law comparison_bit_successor:
  for b: Bool
  for c: Cmp
  {Cmp.is_le(Word.cmp.fin(b, False{}, c)) ==
    Cmp.is_lt(Word.cmp.fin(b, True{}, c)) : Bool}
def comparison_bit_successor(b, c):
  match b c:
    case _ LT{}:
      {==}
    case _ GT{}:
      {==}
    case False{} EQ{}:
      {==}
    case True{} EQ{}:
      {==}

# Comparing one bit with the extremes leaves these tail predicates unchanged.
def comparison_until_one(b: Bool, c: Cmp) ->
  {Cmp.is_le(Word.cmp.fin(b, True{}, c)) == Cmp.is_le(c) : Bool}:
  match b c:
    case _ LT{}: {==}
    case _ GT{}: {==}
    case False{} EQ{}: {==}
    case True{} EQ{}: {==}

def comparison_after_zero(b: Bool, c: Cmp) ->
  {Cmp.is_lt(Word.cmp.fin(b, False{}, c)) == Cmp.is_lt(c) : Bool}:
  match b c:
    case _ LT{}: {==}
    case _ GT{}: {==}
    case False{} EQ{}: {==}
    case True{} EQ{}: {==}

law comparison_bit_transport:
  for b: Bool
  for c: Cmp
  for d: Cmp
  for e: {Cmp.is_le(c) == Cmp.is_lt(d) : Bool}
  {Cmp.is_le(Word.cmp.fin(b, True{}, c)) ==
    Cmp.is_lt(Word.cmp.fin(b, False{}, d)) : Bool}
def comparison_bit_transport(b, c, d, e):
  match b:
    case False{}:
      %Equal.sym(Bool, Cmp.is_le(Word.cmp.fin(False{}, True{}, c)), Cmp.is_le(c),
        comparison_until_one(False{}, c)) : {_ == Cmp.is_lt(Word.cmp.fin(False{}, False{}, d)) : Bool}
      %Equal.sym(Bool, Cmp.is_lt(Word.cmp.fin(False{}, False{}, d)), Cmp.is_lt(d),
        comparison_after_zero(False{}, d)) : {Cmp.is_le(c) == _ : Bool}
      e
    case True{}:
      %Equal.sym(Bool, Cmp.is_le(Word.cmp.fin(True{}, True{}, c)), Cmp.is_le(c),
        comparison_until_one(True{}, c)) : {_ == Cmp.is_lt(Word.cmp.fin(True{}, False{}, d)) : Bool}
      %Equal.sym(Bool, Cmp.is_lt(Word.cmp.fin(True{}, False{}, d)), Cmp.is_lt(d),
        comparison_after_zero(True{}, d)) : {Cmp.is_le(c) == _ : Bool}
      e

law word_limit_successor:
  for +n: Nat
  for +x: Word(n)
  for +y: Word(n)
  for fits: {without_transport(n, y) == True{} : Bool}
  {Cmp.is_le(Word.cmp(n, x, y)) == Cmp.is_lt(Word.cmp(n, x, Word.inc(n, y))) : Bool}
def word_limit_successor(n, x, y, fits):
  match n:
    case 0n:
      F.absurd_boolean({Cmp.is_le(Word.cmp(0n, x, y)) == Cmp.is_lt(Word.cmp(0n, x, Word.inc(0n, y))) : Bool}, fits)
    case 1n+p:
      match x y:
        case WCon{b, +xt} WCon{False{}, +yt}:
          comparison_bit_successor(b, Word.cmp(p, xt, yt))
        case WCon{b, +xt} WCon{True{}, +yt}:
          comparison_bit_transport(b, Word.cmp(p, xt, yt), Word.cmp(p, xt, Word.inc(p, yt)), word_limit_successor(p, xt, yt, fits))

law comparisons_complementary:
  for c: Cmp
  for d: Cmp
  for e: {Cmp.is_le(c) == Cmp.is_lt(d) : Bool}
  {Cmp.is_gt(c) == Cmp.is_ge(d) : Bool}
def comparisons_complementary(c, d, e):
  match c d:
    case LT{} LT{}:
      {==}
    case EQ{} LT{}:
      {==}
    case GT{} EQ{}:
      {==}
    case GT{} GT{}:
      {==}
    case GT{} LT{}:
      Equal.sym(Bool, Cmp.is_le(c), Cmp.is_lt(d), e)
    case LT{} EQ{}:
      Equal.sym(Bool, Cmp.is_le(c), Cmp.is_lt(d), e)
    case LT{} GT{}:
      Equal.sym(Bool, Cmp.is_le(c), Cmp.is_lt(d), e)
    case EQ{} EQ{}:
      Equal.sym(Bool, Cmp.is_le(c), Cmp.is_lt(d), e)
    case EQ{} GT{}:
      Equal.sym(Bool, Cmp.is_le(c), Cmp.is_lt(d), e)

def bits(x: U32) -> Word(32n):
  U32{w} = x
  w

law limit_u32_successor:
  for x: U32
  for y: U32
  for fits: {without_transport(32n, bits(y)) == True{} : Bool}
  {U32.is_le(x, y) == U32.is_lt(x, U32{Word.inc(32n, bits(y))}) : Bool}
def limit_u32_successor(x, y, fits):
  match x y:
    case U32{a} U32{b}:
      word_limit_successor(32n, a, b, fits)

law predicates_unicode_agree:
  for +cp: U32
  {B.code_valid(cp) == D.scalar_valid(cp) : Bool}
def predicates_unicode_agree(cp):
  %Equal.sym(Bool, U32.is_le(cp, 1114111), U32.is_lt(cp, 1114112), limit_u32_successor(cp, 1114111, {==})) :
    {_ && (U32.is_lt(cp, 55296) || U32.is_gt(cp, 57343)) == D.scalar_valid(cp) : Bool}
  %Equal.sym(Bool, U32.is_gt(cp, 57343), U32.is_ge(cp, 57344),
    comparisons_complementary(U32.cmp(cp, 57343), U32.cmp(cp, 57344), limit_u32_successor(cp, 57343, {==}))) :
    {U32.is_lt(cp, 1114112) && (U32.is_lt(cp, 55296) || _) == D.scalar_valid(cp) : Bool}
  {==}

law u32_lt_transitive:
  for +a: U32
  for +b: U32
  for +c: U32
  for ab: {U32.is_lt(a, b) == True{} : Bool}
  for bc: {U32.is_lt(b, c) == True{} : Bool}
  {U32.is_lt(a, c) == True{} : Bool}
def u32_lt_transitive(a, b, c, ab, bc):
  h1 = {(%O.cmp_lt(U32.cmp(a, b), ab) : O.Coherent(_, U32.cmp(b, c), U32.cmp(a, c))
    O.u32_coherent(a, b, c)) : O.Coherent(LT{}, U32.cmp(b, c), U32.cmp(a, c))}
  h2 = {(%O.cmp_lt(U32.cmp(b, c), bc) : O.Coherent(LT{}, _, U32.cmp(a, c))
    h1) : O.Coherent(LT{}, LT{}, U32.cmp(a, c))}
  Equal.cong(Cmp, Bool, k => Cmp.is_lt(k), U32.cmp(a, c), LT{}, h2)

law ascii_and_scalar:
  for +cp: U32
  for ascii: {U32.is_lt(cp, 128) == True{} : Bool}
  {D.scalar_valid(cp) == True{} : Bool}
def ascii_and_scalar(cp, ascii):
  +less = u32_lt_transitive(cp, 128, 55296, ascii, {==})
  greater = u32_lt_transitive(cp, 55296, 1114112, less, {==})
  %Equal.sym(Bool, U32.is_lt(cp, 1114112), True{}, greater) : {_ && (U32.is_lt(cp, 55296) || U32.is_ge(cp, 57344)) == True{} : Bool}
  %Equal.sym(Bool, U32.is_lt(cp, 55296), True{}, less) : {True{} && (_ || U32.is_ge(cp, 57344)) == True{} : Bool}
  {==}

def ScalarValid(e: C.Scalar) -> Type:
  match e:
    case C.Character{cp}:
      {D.scalar_valid(cp) == True{} : Bool}
    case _:
      Unit

law scalar_checked_valid:
  for +ok: Bool
  for +cp: U32
  for valid: {ok == True{} : Bool} -> {B.code_valid(cp) == True{} : Bool}
  ScalarValid(C.scalar_checked(ok, cp))
def scalar_checked_valid(ok, cp, valid):
  match ok:
    case False{}:
      Unit{}
    case True{}:
      Equal.trans(Bool, D.scalar_valid(cp), B.code_valid(cp), True{}, Equal.sym(Bool, B.code_valid(cp), D.scalar_valid(cp), predicates_unicode_agree(cp)), valid({==}))

law complete_utf8_emits_scalar_valid:
  for n: Nat
  for +cp: U32
  for +minimum: U32
  ScalarValid(C.complete_utf8(n, cp, minimum))
def complete_utf8_emits_scalar_valid(n, cp, minimum):
  match n:
    case 0n:
      scalar_checked_valid(U32.is_ge(cp, minimum) && B.code_valid(cp), cp,
        e => F.and_boolean_right(U32.is_ge(cp, minimum), B.code_valid(cp), e))
    case 1n+p:
      Unit{}

law resume_utf8_emits_scalar_valid:
  for ok: Bool
  for n: Nat
  for cp: U32
  for minimum: U32
  for b: U32
  ScalarValid(C.resume_utf8(ok, n, cp, minimum, b))
def resume_utf8_emits_scalar_valid(ok, n, cp, minimum, b):
  match ok:
    case False{}:
      Unit{}
    case True{}:
      complete_utf8_emits_scalar_valid(n, (cp * 64 + b - 128 : U32), minimum)

law start_utf8_emits_scalar_valid:
  for +ascii: Bool
  for two: Bool
  for three: Bool
  for four: Bool
  for +b: U32
  for e: {ascii == True{} : Bool} -> {U32.is_lt(b, 128) == True{} : Bool}
  ScalarValid(C.start_utf8(ascii, two, three, four, b))
def start_utf8_emits_scalar_valid(ascii, two, three, four, b, e):
  match ascii two three four:
    case True{} _ _ _:
      ascii_and_scalar(b, e({==}))
    case False{} True{} _ _:
      Unit{}
    case False{} False{} True{} _:
      Unit{}
    case False{} False{} False{} True{}:
      Unit{}
    case False{} False{} False{} False{}:
      Unit{}

law step_utf8_only_emits_scalars_all_valid:
  for u: C.Unicode
  for +b: U32
  ScalarValid(C.step_utf8(u, b))
def step_utf8_only_emits_scalars_all_valid(u, b):
  match u:
    case C.Start{}:
      start_utf8_emits_scalar_valid(U32.is_lt(b, 128), U32.is_ge(b, 194) && U32.is_le(b, 223), U32.is_ge(b, 224) && U32.is_le(b, 239), U32.is_ge(b, 240) && U32.is_le(b, 244), b, e => e)
    case C.Continue{0n, cp, minimum}:
      Unit{}
    case C.Continue{1n+p, cp, minimum}:
      resume_utf8_emits_scalar_valid(U32.is_ge(b, 128) && U32.is_le(b, 191), p, cp, minimum, b)

law reverse_preserves_unicode_accumulated:
  for +s: String
  for +acc: String
  for +is_valid: {D.unicode_valid(s) == True{} : Bool}
  for accumulated: {D.unicode_valid(acc) == True{} : Bool}
  {D.unicode_valid(String.reverse.go(s, acc)) == True{} : Bool}
def reverse_preserves_unicode_accumulated(s, acc, is_valid, accumulated):
  match s:
    case SNil{}:
      accumulated
    case SCon{Chr{+cp}, +t}:
      reverse_preserves_unicode_accumulated(t, SCon{Chr{cp}, acc},
        F.and_boolean_right(D.scalar_valid(cp), D.unicode_valid(t), is_valid),
        F.and_boolean_intro(D.scalar_valid(cp), D.unicode_valid(acc),
          F.and_boolean_left(D.scalar_valid(cp), D.unicode_valid(t), is_valid), accumulated))

law reverse_preserves_unicode:
  for +s: String
  for +is_valid: {D.unicode_valid(s) == True{} : Bool}
  {D.unicode_valid(String.reverse(s)) == True{} : Bool}
def reverse_preserves_unicode(s, is_valid):
  reverse_preserves_unicode_accumulated(s, "", is_valid, {==})
