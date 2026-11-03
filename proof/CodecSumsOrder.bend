# Mathematical order of representable counters, in both directions.
import Base
import ../contract/Bytes.bend as B
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./CodecCounters.bend as N
import ./CodecUnicode.bend as U
import ./CodecMinimum.bend as M
import ./CodecSums.bend as A

def invert_cmp(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

law invert_fin:
  for a: Bool
  for b: Bool
  for c: Cmp
  {invert_cmp(Word.cmp.fin(a, b, c)) == Word.cmp.fin(b, a, invert_cmp(c)) : Cmp}
def invert_fin(a, b, c):
  match a b c:
    case _ _ LT{}:
      {==}
    case _ _ GT{}:
      {==}
    case False{} False{} EQ{}:
      {==}
    case False{} True{} EQ{}:
      {==}
    case True{} False{} EQ{}:
      {==}
    case True{} True{} EQ{}:
      {==}

law compare_words_inverted:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {invert_cmp(Word.cmp(n, a, b)) == Word.cmp(n, b, a) : Cmp}
def compare_words_inverted(n, a, b):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b:
        case WCon{x, +at} WCon{y, +bt}:
          Equal.trans(Cmp,
            invert_cmp(Word.cmp.fin(x, y, Word.cmp(p, at, bt))),
            Word.cmp.fin(y, x, invert_cmp(Word.cmp(p, at, bt))),
            Word.cmp.fin(y, x, Word.cmp(p, bt, at)),
            invert_fin(x, y, Word.cmp(p, at, bt)),
            Equal.cong(Cmp, Cmp, c => Word.cmp.fin(y, x, c),
              invert_cmp(Word.cmp(p, at, bt)), Word.cmp(p, bt, at), compare_words_inverted(p, at, bt)))

law reads_cmp_inverted:
  for c: Cmp
  {Cmp.is_le(invert_cmp(c)) == Bool.not(Cmp.is_lt(c)) : Bool}
def reads_cmp_inverted(c):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

law lt_cmp_inverted:
  for c: Cmp
  {Cmp.is_lt(invert_cmp(c)) == Bool.not(Cmp.is_le(c)) : Bool}
def lt_cmp_inverted(c):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

law reads_words_inverted:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Cmp.is_le(Word.cmp(n, a, b)) == Bool.not(Cmp.is_lt(Word.cmp(n, b, a))) : Bool}
def reads_words_inverted(n, a, b):
  %compare_words_inverted(n, b, a) :
    {Cmp.is_le(_) == Bool.not(Cmp.is_lt(Word.cmp(n, b, a))) : Bool}
  reads_cmp_inverted(Word.cmp(n, b, a))

law lt_words_inverted:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {Cmp.is_lt(Word.cmp(n, a, b)) == Bool.not(Cmp.is_le(Word.cmp(n, b, a))) : Bool}
def lt_words_inverted(n, a, b):
  %compare_words_inverted(n, b, a) :
    {Cmp.is_lt(_) == Bool.not(Cmp.is_le(Word.cmp(n, b, a))) : Bool}
  lt_cmp_inverted(Word.cmp(n, b, a))

law limit_successor_left:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for fits: {U.without_transport(n, a) == True{} : Bool}
  {Cmp.is_le(Word.cmp(n, Word.inc(n, a), b)) == Cmp.is_lt(Word.cmp(n, a, b)) : Bool}
def limit_successor_left(n, a, b, fits):
  Equal.trans(Bool,
    Cmp.is_le(Word.cmp(n, Word.inc(n, a), b)),
    Bool.not(Cmp.is_lt(Word.cmp(n, b, Word.inc(n, a)))),
    Cmp.is_lt(Word.cmp(n, a, b)),
    reads_words_inverted(n, Word.inc(n, a), b),
    Equal.trans(Bool,
      Bool.not(Cmp.is_lt(Word.cmp(n, b, Word.inc(n, a)))),
      Bool.not(Cmp.is_le(Word.cmp(n, b, a))), Cmp.is_lt(Word.cmp(n, a, b)),
      Equal.cong(Bool, Bool, c => Bool.not(c),
        Cmp.is_lt(Word.cmp(n, b, Word.inc(n, a))), Cmp.is_le(Word.cmp(n, b, a)),
        Equal.sym(Bool, Cmp.is_le(Word.cmp(n, b, a)), Cmp.is_lt(Word.cmp(n, b, Word.inc(n, a))), U.word_limit_successor(n, b, a, fits))),
      Equal.sym(Bool, Cmp.is_lt(Word.cmp(n, a, b)), Bool.not(Cmp.is_le(Word.cmp(n, b, a))), lt_words_inverted(n, a, b))))

law reads_fin_00:
  for c: Cmp
  {Cmp.is_le(Word.cmp.fin(False{}, False{}, c)) == Cmp.is_le(c) : Bool}
def reads_fin_00(c):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

law reads_fin_01:
  for c: Cmp
  {Cmp.is_le(Word.cmp.fin(False{}, True{}, c)) == Cmp.is_le(c) : Bool}
def reads_fin_01(c):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

law reads_fin_10:
  for c: Cmp
  {Cmp.is_le(Word.cmp.fin(True{}, False{}, c)) == Cmp.is_lt(c) : Bool}
def reads_fin_10(c):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

law reads_fin_11:
  for c: Cmp
  {Cmp.is_le(Word.cmp.fin(True{}, True{}, c)) == Cmp.is_le(c) : Bool}
def reads_fin_11(c):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

law increment_preserves_comparison:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +ca: {U.without_transport(n, a) == True{} : Bool}
  for +cb: {U.without_transport(n, b) == True{} : Bool}
  {Cmp.is_le(Word.cmp(n, Word.inc(n, a), Word.inc(n, b))) == Cmp.is_le(Word.cmp(n, a, b)) : Bool}
def increment_preserves_comparison(n, a, b, ca, cb):
  match n:
    case 0n:
      F.absurd_boolean({Cmp.is_le(Word.cmp(0n, Word.inc(0n, a), Word.inc(0n, b))) == Cmp.is_le(Word.cmp(0n, a, b)) : Bool}, ca)
    case 1n+p:
      match a b:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          Equal.trans(Bool,
            Cmp.is_le(Word.cmp.fin(True{}, True{}, Word.cmp(p, at, bt))),
            Cmp.is_le(Word.cmp(p, at, bt)),
            Cmp.is_le(Word.cmp.fin(False{}, False{}, Word.cmp(p, at, bt))),
            reads_fin_11(Word.cmp(p, at, bt)),
            Equal.sym(Bool, Cmp.is_le(Word.cmp.fin(False{}, False{}, Word.cmp(p, at, bt))), Cmp.is_le(Word.cmp(p, at, bt)), reads_fin_00(Word.cmp(p, at, bt))))
        case WCon{False{}, +at} WCon{True{}, +bt}:
          Equal.trans(Bool,
            Cmp.is_le(Word.cmp.fin(True{}, False{}, Word.cmp(p, at, Word.inc(p, bt)))),
            Cmp.is_lt(Word.cmp(p, at, Word.inc(p, bt))),
            Cmp.is_le(Word.cmp.fin(False{}, True{}, Word.cmp(p, at, bt))),
            reads_fin_10(Word.cmp(p, at, Word.inc(p, bt))),
            Equal.trans(Bool,
              Cmp.is_lt(Word.cmp(p, at, Word.inc(p, bt))), Cmp.is_le(Word.cmp(p, at, bt)),
              Cmp.is_le(Word.cmp.fin(False{}, True{}, Word.cmp(p, at, bt))),
              Equal.sym(Bool, Cmp.is_le(Word.cmp(p, at, bt)), Cmp.is_lt(Word.cmp(p, at, Word.inc(p, bt))), U.word_limit_successor(p, at, bt, cb)),
              Equal.sym(Bool, Cmp.is_le(Word.cmp.fin(False{}, True{}, Word.cmp(p, at, bt))), Cmp.is_le(Word.cmp(p, at, bt)), reads_fin_01(Word.cmp(p, at, bt)))))
        case WCon{True{}, +at} WCon{False{}, +bt}:
          Equal.trans(Bool,
            Cmp.is_le(Word.cmp.fin(False{}, True{}, Word.cmp(p, Word.inc(p, at), bt))),
            Cmp.is_le(Word.cmp(p, Word.inc(p, at), bt)),
            Cmp.is_le(Word.cmp.fin(True{}, False{}, Word.cmp(p, at, bt))),
            reads_fin_01(Word.cmp(p, Word.inc(p, at), bt)),
            Equal.trans(Bool,
              Cmp.is_le(Word.cmp(p, Word.inc(p, at), bt)), Cmp.is_lt(Word.cmp(p, at, bt)),
              Cmp.is_le(Word.cmp.fin(True{}, False{}, Word.cmp(p, at, bt))),
              limit_successor_left(p, at, bt, ca),
              Equal.sym(Bool, Cmp.is_le(Word.cmp.fin(True{}, False{}, Word.cmp(p, at, bt))), Cmp.is_lt(Word.cmp(p, at, bt)), reads_fin_10(Word.cmp(p, at, bt)))))
        case WCon{True{}, +at} WCon{True{}, +bt}:
          Equal.trans(Bool,
            Cmp.is_le(Word.cmp.fin(False{}, False{}, Word.cmp(p, Word.inc(p, at), Word.inc(p, bt)))),
            Cmp.is_le(Word.cmp(p, Word.inc(p, at), Word.inc(p, bt))),
            Cmp.is_le(Word.cmp.fin(True{}, True{}, Word.cmp(p, at, bt))),
            reads_fin_00(Word.cmp(p, Word.inc(p, at), Word.inc(p, bt))),
            Equal.trans(Bool,
              Cmp.is_le(Word.cmp(p, Word.inc(p, at), Word.inc(p, bt))), Cmp.is_le(Word.cmp(p, at, bt)),
              Cmp.is_le(Word.cmp.fin(True{}, True{}, Word.cmp(p, at, bt))),
              increment_preserves_comparison(p, at, bt, ca, cb),
              Equal.sym(Bool, Cmp.is_le(Word.cmp.fin(True{}, True{}, Word.cmp(p, at, bt))), Cmp.is_le(Word.cmp(p, at, bt)), reads_fin_11(Word.cmp(p, at, bt)))))

law compare_predecessors_positive:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +pa: {N.zeros(n, a) == False{} : Bool}
  for +pb: {N.zeros(n, b) == False{} : Bool}
  {Cmp.is_le(Word.cmp(n, a, b)) == Cmp.is_le(Word.cmp(n, N.predecessor(n, a), N.predecessor(n, b))) : Bool}
def compare_predecessors_positive(n, a, b, pa, pb):
  %N.increment_of_predecessor(n, a) :
    {Cmp.is_le(Word.cmp(n, _, b)) == Cmp.is_le(Word.cmp(n, N.predecessor(n, a), N.predecessor(n, b))) : Bool}
  %N.increment_of_predecessor(n, b) :
    {Cmp.is_le(Word.cmp(n, Word.inc(n, N.predecessor(n, a)), _)) == Cmp.is_le(Word.cmp(n, N.predecessor(n, a), N.predecessor(n, b))) : Bool}
  increment_preserves_comparison(n, N.predecessor(n, a), N.predecessor(n, b),
    M.predecessor_positive_can_be_incremented(n, a, pa), M.predecessor_positive_can_be_incremented(n, b, pb))

law decrease_preserves_comparison_of_bits:
  for +a: B.Number64
  for +b: B.Number64
  for +pa: {C.zero64(a) == False{} : Bool}
  for +pb: {C.zero64(b) == False{} : Bool}
  {Cmp.is_le(Word.cmp(64n, M.bits64(a), M.bits64(b))) ==
    Cmp.is_le(Word.cmp(64n, M.bits64(C.decrease64(a)), M.bits64(C.decrease64(b)))) : Bool}
def decrease_preserves_comparison_of_bits(a, b, pa, pb):
  %Equal.sym(Word(64n), M.bits64(C.decrease64(a)), N.predecessor(64n, M.bits64(a)), M.decrease64_represents_predecessor_positive(a, pa)) :
    {Cmp.is_le(Word.cmp(64n, M.bits64(a), M.bits64(b))) ==
      Cmp.is_le(Word.cmp(64n, _, M.bits64(C.decrease64(b)))) : Bool}
  %Equal.sym(Word(64n), M.bits64(C.decrease64(b)), N.predecessor(64n, M.bits64(b)), M.decrease64_represents_predecessor_positive(b, pb)) :
    {Cmp.is_le(Word.cmp(64n, M.bits64(a), M.bits64(b))) ==
      Cmp.is_le(Word.cmp(64n, N.predecessor(64n, M.bits64(a)), _)) : Bool}
  compare_predecessors_positive(64n, M.bits64(a), M.bits64(b),
    Equal.trans(Bool, N.zeros(64n, M.bits64(a)), C.zero64(a), False{}, Equal.sym(Bool, C.zero64(a), N.zeros(64n, M.bits64(a)), M.zero64_equivalent_bits_zero(a)), pa),
    Equal.trans(Bool, N.zeros(64n, M.bits64(b)), C.zero64(b), False{}, Equal.sym(Bool, C.zero64(b), N.zeros(64n, M.bits64(b)), M.zero64_equivalent_bits_zero(b)), pb))

# Equivalence, not merely the implication already available in CodecMinimum.
law decrease_preserves_and_reflects_order_positive:
  for +a: B.Number64
  for +b: B.Number64
  for +pa: {C.zero64(a) == False{} : Bool}
  for +pb: {C.zero64(b) == False{} : Bool}
  {C.less_equal64(a, b) == C.less_equal64(C.decrease64(a), C.decrease64(b)) : Bool}
def decrease_preserves_and_reflects_order_positive(a, b, pa, pb):
  Equal.trans(Bool,
    C.less_equal64(a, b), Cmp.is_le(Word.cmp(64n, M.bits64(a), M.bits64(b))),
    C.less_equal64(C.decrease64(a), C.decrease64(b)),
    M.less_equal64_equivalent_order_of_bits(a, b),
    Equal.trans(Bool,
      Cmp.is_le(Word.cmp(64n, M.bits64(a), M.bits64(b))),
      Cmp.is_le(Word.cmp(64n, M.bits64(C.decrease64(a)), M.bits64(C.decrease64(b)))),
      C.less_equal64(C.decrease64(a), C.decrease64(b)),
      decrease_preserves_comparison_of_bits(a, b, pa, pb),
      Equal.sym(Bool, C.less_equal64(C.decrease64(a), C.decrease64(b)),
        Cmp.is_le(Word.cmp(64n, M.bits64(C.decrease64(a)), M.bits64(C.decrease64(b)))), M.less_equal64_equivalent_order_of_bits(C.decrease64(a), C.decrease64(b)))))

law positive_negative_less_equal_zero:
  for +a: B.Number64
  for +positive: {C.zero64(a) == False{} : Bool}
  {C.less_equal64(a, B.Number64{0, 0}) == False{} : Bool}
def positive_negative_less_equal_zero(a, positive):
  N.false_se_true_impossible(C.less_equal64(a, B.Number64{0, 0}), reads =>
    F.false_negative_true(Equal.trans(Bool, False{}, C.zero64(a), True{},
      Equal.sym(Bool, C.zero64(a), False{}, positive), M.less_equal_to_zero64_and_zero(a, reads))))

# Only the two actual measures are premises. All order cases
# (less, equal and greater) follow from mathematical comparison.
law less_equal64_reflects_order_nat:
  for +n: Nat
  for +m: Nat
  for +x: B.Number64
  for +y: B.Number64
  for +nx: {B.nat64(n) == Some{x} : Maybe<&2, B.Number64>}
  for +my: {B.nat64(m) == Some{y} : Maybe<&2, B.Number64>}
  {C.less_equal64(x, y) == Nat.is_le(n, m) : Bool}
def less_equal64_reflects_order_nat(n, m, x, y, nx, my):
  match n m:
    case 0n 0n:
      %F.some_injective(B.Number64, B.Number64{0, 0}, x, nx) :
        {C.less_equal64(_, y) == True{} : Bool}
      M.zero64_negative_greater(y)
    case 0n 1n+q:
      %F.some_injective(B.Number64, B.Number64{0, 0}, x, nx) :
        {C.less_equal64(_, y) == True{} : Bool}
      M.zero64_negative_greater(y)
    case 1n+p 0n:
      %F.some_injective(B.Number64, B.Number64{0, 0}, y, my) :
        {C.less_equal64(x, _) == False{} : Bool}
      positive_negative_less_equal_zero(x, N.nat64_successor_never_zero(p, x, nx))
    case 1n+p 1n+q:
      Equal.trans(Bool,
        C.less_equal64(x, y), C.less_equal64(C.decrease64(x), C.decrease64(y)), Nat.is_le(p, q),
        decrease_preserves_and_reflects_order_positive(x, y, N.nat64_successor_never_zero(p, x, nx), N.nat64_successor_never_zero(q, y, my)),
        less_equal64_reflects_order_nat(p, q, C.decrease64(x), C.decrease64(y),
          N.measure_decremented(p, x, N.nat64_successor_has_predecessor_exact(p, x, nx)),
          N.measure_decremented(q, y, N.nat64_successor_has_predecessor_exact(q, y, my))))

law less_equal64_preserves_order_nat:
  for +n: Nat
  for +m: Nat
  for +x: B.Number64
  for +y: B.Number64
  for +nx: {B.nat64(n) == Some{x} : Maybe<&2, B.Number64>}
  for +my: {B.nat64(m) == Some{y} : Maybe<&2, B.Number64>}
  for reads: {Nat.is_le(n, m) == True{} : Bool}
  {C.less_equal64(x, y) == True{} : Bool}
def less_equal64_preserves_order_nat(n, m, x, y, nx, my, reads):
  Equal.trans(Bool, C.less_equal64(x, y), Nat.is_le(n, m), True{}, less_equal64_reflects_order_nat(n, m, x, y, nx, my), reads)

law check_nat64_exact:
  for +n: Nat
  for +c: Nat
  for +t: Nat
  for +minimum: B.Number64
  for +body: B.Number64
  for +ceiling: B.Number64
  for +mn: {B.nat64(n) == Some{minimum} : Maybe<&2, B.Number64>}
  for +mc: {B.nat64(c) == Some{body} : Maybe<&2, B.Number64>}
  for +mt: {B.nat64(t) == Some{ceiling} : Maybe<&2, B.Number64>}
  {C.check(Some{minimum}, body, ceiling) == C.check_cases(Nat.is_le(n, t), Nat.is_le(n, c)) : C.Check}
def check_nat64_exact(n, c, t, minimum, body, ceiling, mn, mc, mt):
  %Equal.sym(Bool, C.less_equal64(minimum, ceiling), Nat.is_le(n, t), less_equal64_reflects_order_nat(n, t, minimum, ceiling, mn, mt)) :
    {C.check_cases(_, C.less_equal64(minimum, body)) == C.check_cases(Nat.is_le(n, t), Nat.is_le(n, c)) : C.Check}
  Equal.cong(Bool, C.Check, b => C.check_cases(Nat.is_le(n, t), b),
    C.less_equal64(minimum, body), Nat.is_le(n, c), less_equal64_reflects_order_nat(n, c, minimum, body, mn, mc))

law check_nat64_bounded:
  for +n: Nat
  for +c: Nat
  for +t: Nat
  for +minimum: B.Number64
  for +body: B.Number64
  for +ceiling: B.Number64
  for +mn: {B.nat64(n) == Some{minimum} : Maybe<&2, B.Number64>}
  for +mc: {B.nat64(c) == Some{body} : Maybe<&2, B.Number64>}
  for +mt: {B.nat64(t) == Some{ceiling} : Maybe<&2, B.Number64>}
  for nc: {Nat.is_le(n, c) == True{} : Bool}
  for nt: {Nat.is_le(n, t) == True{} : Bool}
  {C.check(Some{minimum}, body, ceiling) == C.Fits{} : C.Check}
def check_nat64_bounded(n, c, t, minimum, body, ceiling, mn, mc, mt, nc, nt):
  Equal.trans(C.Check, C.check(Some{minimum}, body, ceiling), C.check_cases(Nat.is_le(n, t), Nat.is_le(n, c)), C.Fits{},
    check_nat64_exact(n, c, t, minimum, body, ceiling, mn, mc, mt),
    (%Equal.sym(Bool, Nat.is_le(n, t), True{}, nt) : {C.check_cases(_, Nat.is_le(n, c)) == C.Fits{} : C.Check}
      %Equal.sym(Bool, Nat.is_le(n, c), True{}, nc) : {C.check_cases(True{}, _) == C.Fits{} : C.Check}
      {==}))

law nat_subtract_zero:
  for +n: Nat
  {Nat.sub(n, 0n) == n : Nat}
def nat_subtract_zero(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

law nat_decompose_limit:
  for +n: Nat
  for +m: Nat
  for reads: {Nat.is_le(n, m) == True{} : Bool}
  {Nat.add(n, Nat.sub(m, n)) == m : Nat}
def nat_decompose_limit(n, m, reads):
  match n m:
    case 0n _:
      nat_subtract_zero(m)
    case 1n+p 0n:
      F.absurd_boolean({Nat.add(1n+p, Nat.sub(0n, 1n+p)) == 0n : Nat}, reads)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, r => 1n+r, Nat.add(p, Nat.sub(q, p)), q, nat_decompose_limit(p, q, reads))

type NumberRepresented<-m: Maybe<&2, B.Number64>> is Type:
  Represented{number: B.Number64, exact: {m == Some{number} : Maybe<&2, B.Number64>}}

def sum_accepts_requires_first_summand(a: Maybe<&2, B.Number64>, b: Maybe<&2, B.Number64>, -total: B.Number64,
  exact: {C.sum_optional(a, b) == Some{total} : Maybe<&2, B.Number64>}) -> NumberRepresented<a>:
  match a:
    case None{}:
      L.ex_false(NumberRepresented<None{}>, F.none_negative_some(B.Number64, total, exact))
    case Some{x}:
      Represented{x, {==}}

# Representability of the smaller value is DERIVED from the total sum.
law nat64_representability_closed_for_low:
  for +n: Nat
  for +m: Nat
  for +y: B.Number64
  for measured: {B.nat64(m) == Some{y} : Maybe<&2, B.Number64>}
  for reads: {Nat.is_le(n, m) == True{} : Bool}
  NumberRepresented<B.nat64(n)>
def nat64_representability_closed_for_low(n, m, y, measured, reads):
  sum_accepts_requires_first_summand(B.nat64(n), B.nat64(Nat.sub(m, n)), y,
    Equal.trans(Maybe<&2, B.Number64>,
      C.sum_optional(B.nat64(n), B.nat64(Nat.sub(m, n))),
      B.nat64(Nat.add(n, Nat.sub(m, n))), Some{y},
      A.sum_optional_nat64_exact(n, Nat.sub(m, n)),
      Equal.trans(Maybe<&2, B.Number64>, B.nat64(Nat.add(n, Nat.sub(m, n))), B.nat64(m), Some{y},
        Equal.cong(Nat, Maybe<&2, B.Number64>, r => B.nat64(r), Nat.add(n, Nat.sub(m, n)), m, nat_decompose_limit(n, m, reads)), measured)))

def check_natural_represented(+n: Nat, +c: Nat, +t: Nat, +body: B.Number64, +ceiling: B.Number64,
  mc: {B.nat64(c) == Some{body} : Maybe<&2, B.Number64>},
  mt: {B.nat64(t) == Some{ceiling} : Maybe<&2, B.Number64>},
  nc: {Nat.is_le(n, c) == True{} : Bool},
  nt: {Nat.is_le(n, t) == True{} : Bool},
  represented: NumberRepresented<B.nat64(n)>) -> {C.check(B.nat64(n), body, ceiling) == C.Fits{} : C.Check}:
  match represented:
    case Represented{+minimum, +mn}:
      %Equal.sym(Maybe<&2, B.Number64>, B.nat64(n), Some{minimum}, mn) :
        {C.check(_, body, ceiling) == C.Fits{} : C.Check}
      check_nat64_bounded(n, c, t, minimum, body, ceiling, mn, mc, mt, nc, nt)

# This form even eliminates the minimum representability witness.
law check_natural_bounded:
  for +n: Nat
  for +c: Nat
  for +t: Nat
  for +body: B.Number64
  for +ceiling: B.Number64
  for +mc: {B.nat64(c) == Some{body} : Maybe<&2, B.Number64>}
  for +mt: {B.nat64(t) == Some{ceiling} : Maybe<&2, B.Number64>}
  for +nc: {Nat.is_le(n, c) == True{} : Bool}
  for nt: {Nat.is_le(n, t) == True{} : Bool}
  {C.check(B.nat64(n), body, ceiling) == C.Fits{} : C.Check}
def check_natural_bounded(n, c, t, body, ceiling, mc, mt, nc, nt):
  check_natural_represented(n, c, t, body, ceiling, mc, mt, nc, nt, nat64_representability_closed_for_low(n, c, body, mc, nc))
