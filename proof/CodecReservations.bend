# Checks using a natural reserve within the actual body. The ceiling is an
# arbitrary u64: no Nat conversion or minimum-fits assumption is required.
import Base
import ../contract/Bytes.bend as B
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./Orders.bend as O
import ./CodecMinimum.bend as M
import ./CodecSumsOrder.bend as S
import ./CodecSumsMinimum.bend as A

def coherence_reads_reads(ab: Cmp, bc: Cmp, -ac: Cmp,
  h: O.Coherent(ab, bc, ac),
  reads1: {Cmp.is_le(ab) == True{} : Bool},
  reads2: {Cmp.is_le(bc) == True{} : Bool}) -> {Cmp.is_le(ac) == True{} : Bool}:
  match ab bc:
    case EQ{} EQ{}:
      Equal.cong(Cmp, Bool, k => Cmp.is_le(k), ac, EQ{}, h)
    case EQ{} LT{}:
      Equal.cong(Cmp, Bool, k => Cmp.is_le(k), ac, LT{}, h)
    case LT{} EQ{}:
      Equal.cong(Cmp, Bool, k => Cmp.is_le(k), ac, LT{}, h)
    case LT{} LT{}:
      Equal.cong(Cmp, Bool, k => Cmp.is_le(k), ac, LT{}, h)
    case GT{} _:
      F.absurd_boolean({Cmp.is_le(ac) == True{} : Bool}, reads1)
    case EQ{} GT{}:
      F.absurd_boolean({Cmp.is_le(ac) == True{} : Bool}, reads2)
    case LT{} GT{}:
      F.absurd_boolean({Cmp.is_le(ac) == True{} : Bool}, reads2)

law less_equal64_transitive:
  for +a: B.Number64
  for +b: B.Number64
  for +c: B.Number64
  for ab: {C.less_equal64(a, b) == True{} : Bool}
  for bc: {C.less_equal64(b, c) == True{} : Bool}
  {C.less_equal64(a, c) == True{} : Bool}
def less_equal64_transitive(a, b, c, ab, bc):
  Equal.trans(Bool, C.less_equal64(a, c), Cmp.is_le(Word.cmp(64n, M.bits64(a), M.bits64(c))), True{},
    M.less_equal64_equivalent_order_of_bits(a, c),
    coherence_reads_reads(Word.cmp(64n, M.bits64(a), M.bits64(b)), Word.cmp(64n, M.bits64(b), M.bits64(c)), Word.cmp(64n, M.bits64(a), M.bits64(c)),
      O.word_coherent(64n, M.bits64(a), M.bits64(b), M.bits64(c)),
      Equal.trans(Bool, Cmp.is_le(Word.cmp(64n, M.bits64(a), M.bits64(b))), C.less_equal64(a, b), True{},
        Equal.sym(Bool, C.less_equal64(a, b), Cmp.is_le(Word.cmp(64n, M.bits64(a), M.bits64(b))), M.less_equal64_equivalent_order_of_bits(a, b)), ab),
      Equal.trans(Bool, Cmp.is_le(Word.cmp(64n, M.bits64(b), M.bits64(c))), C.less_equal64(b, c), True{},
        Equal.sym(Bool, C.less_equal64(b, c), Cmp.is_le(Word.cmp(64n, M.bits64(b), M.bits64(c))), M.less_equal64_equivalent_order_of_bits(b, c)), bc)))

def check_represented_in_body(+n: Nat, +c: Nat, +body: B.Number64, +ceiling: B.Number64,
  +mc: {B.nat64(c) == Some{body} : Maybe<&2, B.Number64>},
  nc: {Nat.is_le(n, c) == True{} : Bool},
  ct: {C.less_equal64(body, ceiling) == True{} : Bool},
  represented: S.NumberRepresented<B.nat64(n)>) -> {C.check(B.nat64(n), body, ceiling) == C.Fits{} : C.Check}:
  match represented:
    case S.Represented{+minimum, +mn}:
      +fits_body = S.less_equal64_preserves_order_nat(n, c, minimum, body, mn, mc, nc)
      fits_ceiling = less_equal64_transitive(minimum, body, ceiling, fits_body, ct)
      %Equal.sym(Maybe<&2, B.Number64>, B.nat64(n), Some{minimum}, mn) :
        {C.check(_, body, ceiling) == C.Fits{} : C.Check}
      %Equal.sym(Bool, C.less_equal64(minimum, ceiling), True{}, fits_ceiling) :
        {C.check_cases(_, C.less_equal64(minimum, body)) == C.Fits{} : C.Check}
      %Equal.sym(Bool, C.less_equal64(minimum, body), True{}, fits_body) :
        {C.check_cases(True{}, _) == C.Fits{} : C.Check}
      {==}

law minimum_natural_inside_of_body_and_ceiling_u64_fits:
  for +n: Nat
  for +c: Nat
  for +body: B.Number64
  for +ceiling: B.Number64
  for +mc: {B.nat64(c) == Some{body} : Maybe<&2, B.Number64>}
  for +nc: {Nat.is_le(n, c) == True{} : Bool}
  for ct: {C.less_equal64(body, ceiling) == True{} : Bool}
  {C.check(B.nat64(n), body, ceiling) == C.Fits{} : C.Check}
def minimum_natural_inside_of_body_and_ceiling_u64_fits(n, c, body, ceiling, mc, nc, ct):
  check_represented_in_body(n, c, body, ceiling, mc, nc, ct,
    S.nat64_representability_closed_for_low(n, c, body, mc, nc))

law check_minimum_composed_by_body_real:
  for +f: C.Purpose
  for +n: Nat
  for +r: Nat
  for +c: Nat
  for +q: B.Number64
  for +stack: C.Stack
  for +body: B.Number64
  for +ceiling: B.Number64
  for measured: {B.nat64(n) == Some{q} : Maybe<&2, B.Number64>}
  for parent: {C.minimum_stack(stack) == B.nat64(r) : Maybe<&2, B.Number64>}
  for +mc: {B.nat64(c) == Some{body} : Maybe<&2, B.Number64>}
  for nc: {Nat.is_le(Nat.add(A.minimum_field_natural(f, n), r), c) == True{} : Bool}
  for ct: {C.less_equal64(body, ceiling) == True{} : Bool}
  {C.check(C.sum_optional(C.minimum_field(f, q), C.minimum_stack(stack)), body, ceiling) == C.Fits{} : C.Check}
def check_minimum_composed_by_body_real(f, n, r, c, q, stack, body, ceiling, measured, parent, mc, nc, ct):
  %Equal.sym(Maybe<&2, B.Number64>, C.sum_optional(C.minimum_field(f, q), C.minimum_stack(stack)), B.nat64(Nat.add(A.minimum_field_natural(f, n), r)),
    A.minimum_field_combined_stack_nat64_exact(f, n, r, q, stack, measured, parent)) :
    {C.check(_, body, ceiling) == C.Fits{} : C.Check}
  minimum_natural_inside_of_body_and_ceiling_u64_fits(Nat.add(A.minimum_field_natural(f, n), r), c, body, ceiling, mc, nc, ct)
