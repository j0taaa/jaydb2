# Soundness of the actual structural Value comparator.
# Kept separate from runtime helpers so their imports remain unchanged.
import Base
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ./Value.bend as V
import ../proof/Foundations.bend as F
import ../proof/Orders.bend as O

# General correctness of the actual structural comparator. No validity premise:
# malformed list/record tails are compared as structure too.

# Bridge the actual primitive Bool/U32 comparators to propositional equality.
def bool_equal_refl(b: Bool) -> {Bool.not(Bool.xor(b, b)) == True{} : Bool}:
  match b:
    case False{}: {==}
    case True{}: {==}

def bool_equal_sound(a: Bool, b: Bool,
  h: {Bool.not(Bool.xor(a, b)) == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case False{} False{}: {==}
    case True{} True{}: {==}
    case False{} True{}: F.absurd_boolean({False{} == True{} : Bool}, h)
    case True{} False{}: F.absurd_boolean({True{} == False{} : Bool}, h)

def u32_equal_refl(a: U32) -> {U32.is_eq(a, a) == True{} : Bool}:
  Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), U32.cmp(a, a), EQ{}, O.u32_refl(a))

def u32_equal_sound(+a: U32, +b: U32, h: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  O.u32_equal(a, b, O.cmp_eq(U32.cmp(a, b), h))

law equal_reflexive:
  for +v: D.Value
  {V.equal(v, v) == True{} : Bool}
def equal_reflexive(v):
  match v:
    case D.VAbsent{}: {==}
    case D.VBool{b}: bool_equal_refl(b)
    case D.VInt{+h, +l}:
      F.and_boolean_intro(U32.is_eq(h, h), U32.is_eq(l, l), u32_equal_refl(h), u32_equal_refl(l))
    case D.VText{s}: O.string_eq_refl(s)
    case D.VListEmpty{}: {==}
    case D.VList{+x, +xs}:
      F.and_boolean_intro(V.equal(x, x), V.equal(xs, xs), equal_reflexive(x), equal_reflexive(xs))
    case D.VRecordEmpty{}: {==}
    case D.VRecord{+n, +x, +xs}:
      F.and_boolean_intro(String.eq(n, n) && V.equal(x, x), V.equal(xs, xs),
        F.and_boolean_intro(String.eq(n, n), V.equal(x, x), O.string_eq_refl(n), equal_reflexive(x)),
        equal_reflexive(xs))

law equal_sound:
  for +a: D.Value
  for +b: D.Value
  for +h: {V.equal(a, b) == True{} : Bool}
  {a == b : D.Value}
def equal_sound(a, b, h):
  match a b:
    case D.VAbsent{} D.VAbsent{}: {==}
    case D.VBool{+x} D.VBool{+y}:
      Equal.cong(Bool, D.Value, b => D.VBool{b}, x, y, bool_equal_sound(x, y, h))
    case D.VInt{+a, +b} D.VInt{+c, +d}:
      %u32_equal_sound(a, c, F.and_boolean_left(U32.is_eq(a, c), U32.is_eq(b, d), h)) :
        {D.VInt{a, b} == D.VInt{_, d} : D.Value}
      Equal.cong(U32, D.Value, l => D.VInt{a, l}, b, d,
        u32_equal_sound(b, d, F.and_boolean_right(U32.is_eq(a, c), U32.is_eq(b, d), h)))
    case D.VText{+x} D.VText{+y}:
      Equal.cong(String, D.Value, s => D.VText{s}, x, y, O.string_equal(x, y, h))
    case D.VListEmpty{} D.VListEmpty{}: {==}
    case D.VList{+x, +xs} D.VList{+y, +ys}:
      %equal_sound(x, y, F.and_boolean_left(V.equal(x, y), V.equal(xs, ys), h)) :
        {D.VList{x, xs} == D.VList{_, ys} : D.Value}
      Equal.cong(D.Value, D.Value, tail => D.VList{x, tail}, xs, ys,
        equal_sound(xs, ys, F.and_boolean_right(V.equal(x, y), V.equal(xs, ys), h)))
    case D.VRecordEmpty{} D.VRecordEmpty{}: {==}
    case D.VRecord{+n, +x, +xs} D.VRecord{+m, +y, +ys}:
      +first = F.and_boolean_left(String.eq(n, m) && V.equal(x, y), V.equal(xs, ys), h)
      %O.string_equal(n, m, F.and_boolean_left(String.eq(n, m), V.equal(x, y), first)) :
        {D.VRecord{n, x, xs} == D.VRecord{_, y, ys} : D.Value}
      %equal_sound(x, y, F.and_boolean_right(String.eq(n, m), V.equal(x, y), first)) :
        {D.VRecord{n, x, xs} == D.VRecord{n, _, ys} : D.Value}
      Equal.cong(D.Value, D.Value, tail => D.VRecord{n, x, tail}, xs, ys,
        equal_sound(xs, ys, F.and_boolean_right(String.eq(n, m) && V.equal(x, y), V.equal(xs, ys), h)))
    # Split mismatched constructors explicitly: the pinned checker cannot
    # reduce Value.equal on a residual wildcard sum.
    case D.VAbsent{} D.VBool{_}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VAbsent{} D.VInt{_, _}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VAbsent{} D.VText{_}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VAbsent{} D.VListEmpty{}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VAbsent{} D.VList{_, _}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VAbsent{} D.VRecordEmpty{}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VAbsent{} D.VRecord{_, _, _}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VBool{_} D.VAbsent{}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VBool{_} D.VInt{_, _}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VBool{_} D.VText{_}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VBool{_} D.VListEmpty{}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VBool{_} D.VList{_, _}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VBool{_} D.VRecordEmpty{}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VBool{_} D.VRecord{_, _, _}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VInt{_, _} D.VAbsent{}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VInt{_, _} D.VBool{_}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VInt{_, _} D.VText{_}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VInt{_, _} D.VListEmpty{}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VInt{_, _} D.VList{_, _}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VInt{_, _} D.VRecordEmpty{}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VInt{_, _} D.VRecord{_, _, _}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VText{_} D.VAbsent{}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VText{_} D.VBool{_}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VText{_} D.VInt{_, _}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VText{_} D.VListEmpty{}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VText{_} D.VList{_, _}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VText{_} D.VRecordEmpty{}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VText{_} D.VRecord{_, _, _}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VListEmpty{} D.VAbsent{}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VListEmpty{} D.VBool{_}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VListEmpty{} D.VInt{_, _}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VListEmpty{} D.VText{_}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VListEmpty{} D.VList{_, _}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VListEmpty{} D.VRecordEmpty{}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VListEmpty{} D.VRecord{_, _, _}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VList{_, _} D.VAbsent{}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VList{_, _} D.VBool{_}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VList{_, _} D.VInt{_, _}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VList{_, _} D.VText{_}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VList{_, _} D.VListEmpty{}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VList{_, _} D.VRecordEmpty{}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VList{_, _} D.VRecord{_, _, _}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VRecordEmpty{} D.VAbsent{}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VRecordEmpty{} D.VBool{_}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VRecordEmpty{} D.VInt{_, _}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VRecordEmpty{} D.VText{_}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VRecordEmpty{} D.VListEmpty{}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VRecordEmpty{} D.VList{_, _}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VRecordEmpty{} D.VRecord{_, _, _}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VRecord{_, _, _} D.VAbsent{}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VRecord{_, _, _} D.VBool{_}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VRecord{_, _, _} D.VInt{_, _}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VRecord{_, _, _} D.VText{_}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VRecord{_, _, _} D.VListEmpty{}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VRecord{_, _, _} D.VList{_, _}: F.absurd_boolean({a == b : D.Value}, h)
    case D.VRecord{_, _, _} D.VRecordEmpty{}: F.absurd_boolean({a == b : D.Value}, h)

law equal_complete:
  for +a: D.Value
  for +b: D.Value
  for h: {a == b : D.Value}
  {V.equal(a, b) == True{} : Bool}
def equal_complete(a, b, h):
  %h : {V.equal(a, _) == True{} : Bool}
  equal_reflexive(a)

law equal_true_inverse:
  for +a: D.Value
  for +b: D.Value
  for h: {V.equal(a, b) == True{} : Bool}
  {V.equal(b, a) == True{} : Bool}
def equal_true_inverse(a, b, h):
  equal_complete(b, a, Equal.sym(D.Value, a, b, equal_sound(a, b, h)))

# A false comparison proves structural inequality, rather than merely being
# evidence about an implementation-specific predicate.
law unequal_values_differ:
  for +a: D.Value
  for +b: D.Value
  for h: {V.equal(a, b) == False{} : Bool}
  {a == b : D.Value} -> Empty
def unequal_values_differ(a, b, h):
  equal => F.false_negative_true(Equal.trans(Bool, False{}, V.equal(a, b), True{},
    Equal.sym(Bool, V.equal(a, b), False{}, h), equal_complete(a, b, equal)))

