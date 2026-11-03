# Exact body-counter arithmetic: decrement inverts the overflow-free
# conversion in contract/Bytes. Does not materialize 2^32/2^64 as Nat.
import Base
import ../contract/Bytes.bend as B
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./Orders.bend as O
import ./CodecTrace.bend as R

def predecessor(n: Nat, w: Word(n)) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match w:
        case WCon{True{}, t}:
          WCon{False{}, t}
        case WCon{False{}, t}:
          WCon{True{}, predecessor(p, t)}

law predecessor_of_increment:
  for +n: Nat
  for +w: Word(n)
  {predecessor(n, Word.inc(n, w)) == w : Word(n)}
def predecessor_of_increment(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          {==}
        case WCon{True{}, +t}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{True{}, r}, predecessor(p, Word.inc(p, t)), t, predecessor_of_increment(p, t))

law adc_zero_identity:
  for +n: Nat
  for w: Word(n)
  {Word.adc(n, w, Word.zero(n), False{}, False{}) == w : Word(n)}
def adc_zero_identity(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r}, Word.adc(p, t, Word.zero(p), False{}, False{}), t, adc_zero_identity(p, t))
        case WCon{True{}, +t}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{True{}, r}, Word.adc(p, t, Word.zero(p), False{}, False{}), t, adc_zero_identity(p, t))

law adc_zero_increments:
  for +n: Nat
  for +w: Word(n)
  {Word.adc(n, w, Word.zero(n), False{}, True{}) == Word.inc(n, w) : Word(n)}
def adc_zero_increments(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{True{}, r}, Word.adc(p, t, Word.zero(p), False{}, False{}), t, adc_zero_identity(p, t))
        case WCon{True{}, +t}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r}, Word.adc(p, t, Word.zero(p), False{}, True{}), Word.inc(p, t), adc_zero_increments(p, t))

law sbb_zero_identity:
  for +n: Nat
  for w: Word(n)
  {Word.adc(n, w, Word.zero(n), True{}, True{}) == w : Word(n)}
def sbb_zero_identity(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r}, Word.adc(p, t, Word.zero(p), True{}, True{}), t, sbb_zero_identity(p, t))
        case WCon{True{}, +t}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{True{}, r}, Word.adc(p, t, Word.zero(p), True{}, True{}), t, sbb_zero_identity(p, t))

law sbb_zero_decrements:
  for +n: Nat
  for +w: Word(n)
  {Word.adc(n, w, Word.zero(n), True{}, False{}) == predecessor(n, w) : Word(n)}
def sbb_zero_decrements(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{True{}, r}, Word.adc(p, t, Word.zero(p), True{}, False{}), predecessor(p, t), sbb_zero_decrements(p, t))
        case WCon{True{}, +t}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r}, Word.adc(p, t, Word.zero(p), True{}, True{}), t, sbb_zero_identity(p, t))

def one(n: Nat) -> Word(1n+n):
  WCon{True{}, Word.zero(n)}

law sum_one_increments:
  for +n: Nat
  for +w: Word(1n+n)
  {Word.add(1n+n, w, one(n)) == Word.inc(1n+n, w) : Word(1n+n)}
def sum_one_increments(n, w):
  match w:
    case WCon{False{}, +t}:
      Equal.cong(Word(n), Word(1n+n), r => WCon{True{}, r}, Word.adc(n, t, Word.zero(n), False{}, False{}), t, adc_zero_identity(n, t))
    case WCon{True{}, +t}:
      Equal.cong(Word(n), Word(1n+n), r => WCon{False{}, r}, Word.adc(n, t, Word.zero(n), False{}, True{}), Word.inc(n, t), adc_zero_increments(n, t))

law subtract_one_decrements:
  for +n: Nat
  for +w: Word(1n+n)
  {Word.sub(1n+n, w, one(n)) == predecessor(1n+n, w) : Word(1n+n)}
def subtract_one_decrements(n, w):
  match w:
    case WCon{False{}, +t}:
      Equal.cong(Word(n), Word(1n+n), r => WCon{True{}, r}, Word.adc(n, t, Word.zero(n), True{}, False{}), predecessor(n, t), sbb_zero_decrements(n, t))
    case WCon{True{}, +t}:
      Equal.cong(Word(n), Word(1n+n), r => WCon{False{}, r}, Word.adc(n, t, Word.zero(n), True{}, True{}), t, sbb_zero_identity(n, t))

law sum_subtract_one_cancels:
  for +x: U32
  {((x + 1 : U32) - 1 : U32) == x : U32}
def sum_subtract_one_cancels(x):
  match x:
    case U32{+w}:
      %Equal.sym(Word(32n), Word.add(32n, w, one(31n)), Word.inc(32n, w), sum_one_increments(31n, w)) :
        {U32{Word.sub(32n, _, one(31n))} == U32{w} : U32}
      %Equal.sym(Word(32n), Word.sub(32n, Word.inc(32n, w), one(31n)), predecessor(32n, Word.inc(32n, w)), subtract_one_decrements(31n, Word.inc(32n, w))) :
        {U32{_} == U32{w} : U32}
      Equal.cong(Word(32n), U32, r => U32{r}, predecessor(32n, Word.inc(32n, w)), w, predecessor_of_increment(32n, w))

def zeros(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          zeros(p, t)
        case WCon{True{}, t}:
          False{}

def ones(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          False{}
        case WCon{True{}, t}:
          ones(p, t)

def maximum(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{True{}, maximum(p)}

law cmp_zero_bit:
  for b: Bool
  for c: Cmp
  {Cmp.is_eq(Word.cmp.fin(b, False{}, c)) == Bool.not(b) && Cmp.is_eq(c) : Bool}
def cmp_zero_bit(b, c):
  match b c:
    case False{} LT{}:
      {==}
    case False{} EQ{}:
      {==}
    case False{} GT{}:
      {==}
    case True{} LT{}:
      {==}
    case True{} EQ{}:
      {==}
    case True{} GT{}:
      {==}

law cmp_maximum_bit:
  for b: Bool
  for c: Cmp
  {Cmp.is_eq(Word.cmp.fin(b, True{}, c)) == b && Cmp.is_eq(c) : Bool}
def cmp_maximum_bit(b, c):
  match b c:
    case False{} LT{}:
      {==}
    case False{} EQ{}:
      {==}
    case False{} GT{}:
      {==}
    case True{} LT{}:
      {==}
    case True{} EQ{}:
      {==}
    case True{} GT{}:
      {==}

law comparison_zero_recognizes_bits:
  for +n: Nat
  for +w: Word(n)
  {Cmp.is_eq(Word.cmp(n, w, Word.zero(n))) == zeros(n, w) : Bool}
def comparison_zero_recognizes_bits(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, +t}:
          Equal.trans(Bool, Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(p, t, Word.zero(p)))), Cmp.is_eq(Word.cmp(p, t, Word.zero(p))), zeros(p, t),
            cmp_zero_bit(False{}, Word.cmp(p, t, Word.zero(p))), comparison_zero_recognizes_bits(p, t))
        case WCon{True{}, t}:
          cmp_zero_bit(True{}, Word.cmp(p, t, Word.zero(p)))

law comparison_maximum_recognizes_bits:
  for +n: Nat
  for +w: Word(n)
  {Cmp.is_eq(Word.cmp(n, w, maximum(n))) == ones(n, w) : Bool}
def comparison_maximum_recognizes_bits(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          cmp_maximum_bit(False{}, Word.cmp(p, t, maximum(p)))
        case WCon{True{}, +t}:
          Equal.trans(Bool, Cmp.is_eq(Word.cmp.fin(True{}, True{}, Word.cmp(p, t, maximum(p)))), Cmp.is_eq(Word.cmp(p, t, maximum(p))), ones(p, t),
            cmp_maximum_bit(True{}, Word.cmp(p, t, maximum(p))), comparison_maximum_recognizes_bits(p, t))

law increment_zero_exactly_in_maximum:
  for +n: Nat
  for +w: Word(n)
  {zeros(n, Word.inc(n, w)) == ones(n, w) : Bool}
def increment_zero_exactly_in_maximum(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          {==}
        case WCon{True{}, t}:
          increment_zero_exactly_in_maximum(p, t)

law sum_one_zero_exactly_in_maximum:
  for +x: U32
  {U32.is_eq((x + 1 : U32), 0) == U32.is_eq(x, 4294967295) : Bool}
def sum_one_zero_exactly_in_maximum(x):
  match x:
    case U32{+w}:
      %Equal.sym(Word(32n), Word.add(32n, w, one(31n)), Word.inc(32n, w), sum_one_increments(31n, w)) :
        {Cmp.is_eq(Word.cmp(32n, _, Word.zero(32n))) == Cmp.is_eq(Word.cmp(32n, w, maximum(32n))) : Bool}
      Equal.trans(Bool, Cmp.is_eq(Word.cmp(32n, Word.inc(32n, w), Word.zero(32n))), zeros(32n, Word.inc(32n, w)), Cmp.is_eq(Word.cmp(32n, w, maximum(32n))),
        comparison_zero_recognizes_bits(32n, Word.inc(32n, w)),
        Equal.trans(Bool, zeros(32n, Word.inc(32n, w)), ones(32n, w), Cmp.is_eq(Word.cmp(32n, w, maximum(32n))), increment_zero_exactly_in_maximum(32n, w),
          Equal.sym(Bool, Cmp.is_eq(Word.cmp(32n, w, maximum(32n))), ones(32n, w), comparison_maximum_recognizes_bits(32n, w))))

law equality_u32:
  for +x: U32
  for +y: U32
  for e: {U32.is_eq(x, y) == True{} : Bool}
  {x == y : U32}
def equality_u32(x, y, e):
  O.u32_equal(x, y, O.cmp_eq(U32.cmp(x, y), e))

law decrease_without_transport_inverts_increment:
  for +a: U32
  for +b: U32
  for negative_maximum: {U32.is_eq(b, 4294967295) == False{} : Bool}
  {C.decrease64(B.Number64{a, (b + 1 : U32)}) == B.Number64{a, b} : B.Number64}
def decrease_without_transport_inverts_increment(a, b, negative_maximum):
  %Equal.sym(Bool, U32.is_eq((b + 1 : U32), 0), False{},
    Equal.trans(Bool, U32.is_eq((b + 1 : U32), 0), U32.is_eq(b, 4294967295), False{}, sum_one_zero_exactly_in_maximum(b), negative_maximum)) :
    {C.decrease64_cases(_, U32.is_eq(a, 0), a, (b + 1 : U32)) == B.Number64{a, b} : B.Number64}
  Equal.cong(U32, B.Number64, r => B.Number64{a, r}, ((b + 1 : U32) - 1 : U32), b, sum_subtract_one_cancels(b))

law decrease_combined_transport_inverts_increment:
  for +a: U32
  for +b: U32
  for maximum_b: {U32.is_eq(b, 4294967295) == True{} : Bool}
  for negative_maximum_to: {U32.is_eq(a, 4294967295) == False{} : Bool}
  {C.decrease64(B.Number64{(a + 1 : U32), 0}) == B.Number64{a, b} : B.Number64}
def decrease_combined_transport_inverts_increment(a, b, maximum_b, negative_maximum_to):
  %Equal.sym(Bool, U32.is_eq((a + 1 : U32), 0), False{},
    Equal.trans(Bool, U32.is_eq((a + 1 : U32), 0), U32.is_eq(a, 4294967295), False{}, sum_one_zero_exactly_in_maximum(a), negative_maximum_to)) :
    {C.decrease64_cases(True{}, _, (a + 1 : U32), 0) == B.Number64{a, b} : B.Number64}
  %Equal.sym(U32, b, 4294967295, equality_u32(b, 4294967295, maximum_b)) :
    {B.Number64{((a + 1 : U32) - 1 : U32), 4294967295} == B.Number64{a, _} : B.Number64}
  Equal.cong(U32, B.Number64, r => B.Number64{r, 4294967295}, ((a + 1 : U32) - 1 : U32), a, sum_subtract_one_cancels(a))

law increment64_cases_has_predecessor_exact:
  for transport: Bool
  for exhausted: Bool
  for +a: U32
  for +b: U32
  for -y: B.Number64
  for eb: {U32.is_eq(b, 4294967295) == transport : Bool}
  for ea: {U32.is_eq(a, 4294967295) == exhausted : Bool}
  for increment: {B.increment64_cases(a, b, transport, exhausted) == Some{y} : Maybe<&2, B.Number64>}
  {C.decrease64(y) == B.Number64{a, b} : B.Number64}
def increment64_cases_has_predecessor_exact(transport, exhausted, a, b, y, eb, ea, increment):
  match transport exhausted:
    case False{} _:
      %F.some_injective(B.Number64, B.Number64{a, (b + 1 : U32)}, y, increment) :
        {C.decrease64(_) == B.Number64{a, b} : B.Number64}
      decrease_without_transport_inverts_increment(a, b, eb)
    case True{} False{}:
      %F.some_injective(B.Number64, B.Number64{(a + 1 : U32), 0}, y, increment) :
        {C.decrease64(_) == B.Number64{a, b} : B.Number64}
      decrease_combined_transport_inverts_increment(a, b, eb, ea)
    case True{} True{}:
      L.ex_false({C.decrease64(y) == B.Number64{a, b} : B.Number64}, F.none_negative_some(B.Number64, y, increment))

law increment64_has_predecessor_exact:
  for +x: B.Number64
  for -y: B.Number64
  for increment: {B.increment64(Some{x}) == Some{y} : Maybe<&2, B.Number64>}
  {C.decrease64(y) == x : B.Number64}
def increment64_has_predecessor_exact(x, y, increment):
  match x:
    case B.Number64{+a, +b}:
      increment64_cases_has_predecessor_exact(U32.is_eq(b, 4294967295), U32.is_eq(a, 4294967295), a, b, y, {==}, {==}, increment)

# Predecessor existence follows from the result, not an assumption.
type Predecessor<-previous: Maybe<&2, B.Number64>, -current: B.Number64> is Type:
  Predecessor{number: B.Number64,
    measured: {previous == Some{number} : Maybe<&2, B.Number64>},
    decrement: {C.decrease64(current) == number : B.Number64}}

law invert_increment_accepted:
  for previous: Maybe<&2, B.Number64>
  for -current: B.Number64
  for increment: {B.increment64(previous) == Some{current} : Maybe<&2, B.Number64>}
  Predecessor<previous, current>
def invert_increment_accepted(previous, current, increment):
  match previous:
    case None{}:
      L.ex_false(Predecessor<None{}, current>, F.none_negative_some(B.Number64, current, increment))
    case Some{+x}:
      Predecessor{x, {==}, increment64_has_predecessor_exact(x, current, increment)}

law nat64_successor_has_predecessor_exact:
  for +n: Nat
  for -current: B.Number64
  for measured: {B.nat64(1n+n) == Some{current} : Maybe<&2, B.Number64>}
  Predecessor<B.nat64(n), current>
def nat64_successor_has_predecessor_exact(n, current, measured):
  invert_increment_accepted(B.nat64(n), current, measured)

# Every consumed byte preserves the EXACT measure of the remaining body.
def measure_decremented(-n: Nat, -current: B.Number64, proofs: Predecessor<B.nat64(n), current>) ->
  {B.nat64(n) == Some{C.decrease64(current)} : Maybe<&2, B.Number64>}:
  match proofs:
    case Predecessor{number, measured, decrement}:
      %Equal.sym(B.Number64, C.decrease64(current), number, decrement) :
        {B.nat64(n) == Some{_} : Maybe<&2, B.Number64>}
      measured

law length_of_tail_and_decrement_of_body:
  for +b: U32
  for +bs: List<&2, U32>
  for -body: B.Number64
  for measured: {B.nat64(B.length(Con{b, bs})) == Some{body} : Maybe<&2, B.Number64>}
  {B.nat64(B.length(bs)) == Some{C.decrease64(body)} : Maybe<&2, B.Number64>}
def length_of_tail_and_decrement_of_body(b, bs, body, measured):
  measure_decremented(B.length(bs), body, nat64_successor_has_predecessor_exact(B.length(bs), body, measured))

law and_false_right:
  for b: Bool
  {b && False{} == False{} : Bool}
def and_false_right(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

law increment_without_transport_negative_zero:
  for +a: U32
  for +b: U32
  for negative_maximum: {U32.is_eq(b, 4294967295) == False{} : Bool}
  {C.zero64(B.Number64{a, (b + 1 : U32)}) == False{} : Bool}
def increment_without_transport_negative_zero(a, b, negative_maximum):
  %Equal.sym(Bool, U32.is_eq((b + 1 : U32), 0), False{},
    Equal.trans(Bool, U32.is_eq((b + 1 : U32), 0), U32.is_eq(b, 4294967295), False{}, sum_one_zero_exactly_in_maximum(b), negative_maximum)) :
    {U32.is_eq(a, 0) && _ == False{} : Bool}
  and_false_right(U32.is_eq(a, 0))

law increment_combined_transport_negative_zero:
  for +a: U32
  for negative_maximum: {U32.is_eq(a, 4294967295) == False{} : Bool}
  {C.zero64(B.Number64{(a + 1 : U32), 0}) == False{} : Bool}
def increment_combined_transport_negative_zero(a, negative_maximum):
  %Equal.sym(Bool, U32.is_eq((a + 1 : U32), 0), False{},
    Equal.trans(Bool, U32.is_eq((a + 1 : U32), 0), U32.is_eq(a, 4294967295), False{}, sum_one_zero_exactly_in_maximum(a), negative_maximum)) :
    {_ && True{} == False{} : Bool}
  {==}

law increment64_cases_never_wraps_for_zero:
  for transport: Bool
  for exhausted: Bool
  for +a: U32
  for +b: U32
  for -y: B.Number64
  for eb: {U32.is_eq(b, 4294967295) == transport : Bool}
  for ea: {U32.is_eq(a, 4294967295) == exhausted : Bool}
  for increment: {B.increment64_cases(a, b, transport, exhausted) == Some{y} : Maybe<&2, B.Number64>}
  {C.zero64(y) == False{} : Bool}
def increment64_cases_never_wraps_for_zero(transport, exhausted, a, b, y, eb, ea, increment):
  match transport exhausted:
    case False{} _:
      %F.some_injective(B.Number64, B.Number64{a, (b + 1 : U32)}, y, increment) : {C.zero64(_) == False{} : Bool}
      increment_without_transport_negative_zero(a, b, eb)
    case True{} False{}:
      %F.some_injective(B.Number64, B.Number64{(a + 1 : U32), 0}, y, increment) : {C.zero64(_) == False{} : Bool}
      increment_combined_transport_negative_zero(a, ea)
    case True{} True{}:
      L.ex_false({C.zero64(y) == False{} : Bool}, F.none_negative_some(B.Number64, y, increment))

law increment_accepted_never_wraps_for_zero:
  for previous: Maybe<&2, B.Number64>
  for -y: B.Number64
  for increment: {B.increment64(previous) == Some{y} : Maybe<&2, B.Number64>}
  {C.zero64(y) == False{} : Bool}
def increment_accepted_never_wraps_for_zero(previous, y, increment):
  match previous:
    case None{}:
      L.ex_false({C.zero64(y) == False{} : Bool}, F.none_negative_some(B.Number64, y, increment))
    case Some{B.Number64{+a, +b}}:
      increment64_cases_never_wraps_for_zero(U32.is_eq(b, 4294967295), U32.is_eq(a, 4294967295), a, b, y, {==}, {==}, increment)

law nat64_successor_never_zero:
  for n: Nat
  for -current: B.Number64
  for measured: {B.nat64(1n+n) == Some{current} : Maybe<&2, B.Number64>}
  {C.zero64(current) == False{} : Bool}
def nat64_successor_never_zero(n, current, measured):
  increment_accepted_never_wraps_for_zero(B.nat64(n), current, measured)

def zero_and_negative_zero(-x: B.Number64,
  zero: {x == B.Number64{0, 0} : B.Number64},
  negative_zero: {C.zero64(x) == False{} : Bool}) -> Empty:
  F.false_negative_true(Equal.sym(Bool, True{}, False{},
    (%zero : {C.zero64(_) == False{} : Bool}
      negative_zero)))

law nat64_and_injective_in_results_representable:
  for +a: Nat
  for +b: Nat
  for -number: B.Number64
  for ma: {B.nat64(a) == Some{number} : Maybe<&2, B.Number64>}
  for mb: {B.nat64(b) == Some{number} : Maybe<&2, B.Number64>}
  {a == b : Nat}
def nat64_and_injective_in_results_representable(a, b, number, ma, mb):
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+p:
      L.ex_false({0n == 1n+p : Nat}, zero_and_negative_zero(number,
        Equal.sym(B.Number64, B.Number64{0, 0}, number, F.some_injective(B.Number64, B.Number64{0, 0}, number, ma)), nat64_successor_never_zero(p, number, mb)))
    case 1n+p 0n:
      L.ex_false({1n+p == 0n : Nat}, zero_and_negative_zero(number,
        Equal.sym(B.Number64, B.Number64{0, 0}, number, F.some_injective(B.Number64, B.Number64{0, 0}, number, mb)), nat64_successor_never_zero(p, number, ma)))
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q,
        nat64_and_injective_in_results_representable(p, q, C.decrease64(number),
          measure_decremented(p, number, nat64_successor_has_predecessor_exact(p, number, ma)),
          measure_decremented(q, number, nat64_successor_has_predecessor_exact(q, number, mb))))

law zero64_reflects_count_natural:
  for n: Nat
  for -number: B.Number64
  for measured: {B.nat64(n) == Some{number} : Maybe<&2, B.Number64>}
  {C.zero64(number) == Nat.is_eq(n, 0n) : Bool}
def zero64_reflects_count_natural(n, number, measured):
  match n:
    case 0n:
      %F.some_injective(B.Number64, B.Number64{0, 0}, number, measured) : {C.zero64(_) == True{} : Bool}
      {==}
    case 1n+p:
      nat64_successor_never_zero(p, number, measured)

law one64_only_recognizes_one:
  for +number: B.Number64
  for +e: {C.one64(number) == True{} : Bool}
  {number == B.Number64{0, 1} : B.Number64}
def one64_only_recognizes_one(number, e):
  match number:
    case B.Number64{+a, +b}:
      %Equal.sym(U32, a, 0, equality_u32(a, 0, F.and_boolean_left(U32.is_eq(a, 0), U32.is_eq(b, 1), e))) :
        {B.Number64{_, b} == B.Number64{0, 1} : B.Number64}
      Equal.cong(U32, B.Number64, x => B.Number64{0, x}, b, 1,
        equality_u32(b, 1, F.and_boolean_right(U32.is_eq(a, 0), U32.is_eq(b, 1), e)))

law false_se_true_impossible:
  for +b: Bool
  for impossible: {b == True{} : Bool} -> Empty
  {b == False{} : Bool}
def false_se_true_impossible(b, impossible):
  match b:
    case False{}:
      {==}
    case True{}:
      L.ex_false({True{} == False{} : Bool}, impossible({==}))

law one64_reflects_count_natural:
  for +n: Nat
  for +number: B.Number64
  for measured: {B.nat64(n) == Some{number} : Maybe<&2, B.Number64>}
  {C.one64(number) == Nat.is_eq(n, 1n) : Bool}
def one64_reflects_count_natural(n, number, measured):
  match n:
    case 0n:
      %F.some_injective(B.Number64, B.Number64{0, 0}, number, measured) : {C.one64(_) == False{} : Bool}
      {==}
    case 1n:
      %F.some_injective(B.Number64, B.Number64{0, 1}, number, measured) : {C.one64(_) == True{} : Bool}
      {==}
    case 2n+p:
      false_se_true_impossible(C.one64(number), e =>
        F.false_negative_true(Equal.cong(Nat, Bool, k => Nat.is_eq(k, 1n), 2n+p, 1n,
          nat64_and_injective_in_results_representable(2n+p, 1n, B.Number64{0, 1},
            (%one64_only_recognizes_one(number, e) : {B.nat64(2n+p) == Some{_} : Maybe<&2, B.Number64>}
              measured), {==}))))


def body_frame(q: R.Frame) -> B.Number64:
  R.Frame{body, ceiling, m} = q
  body

law counter_of_body_measures_exactly_o_suffix:
  for xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for +m: C.Machine
  for measured: {B.nat64(B.length(B.concatenate(xs, ys))) == Some{body} : Maybe<&2, B.Number64>}
  {B.nat64(B.length(ys)) == Some{body_frame(R.execute(xs, R.Frame{body, ceiling, m}))} : Maybe<&2, B.Number64>}
def counter_of_body_measures_exactly_o_suffix(xs, ys, body, ceiling, m, measured):
  match xs:
    case Nil{}:
      measured
    case Con{+b, +t}:
      +rest = C.decrease64(body)
      +free = C.decrease64(ceiling)
      counter_of_body_measures_exactly_o_suffix(t, ys, rest, free, C.step(m, b, rest, free),
        measure_decremented(B.length(B.concatenate(t, ys)), body,
          nat64_successor_has_predecessor_exact(B.length(B.concatenate(t, ys)), body, measured)))

law consumption_integral_exhausts_exactly_o_body:
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for +m: C.Machine
  for measured: {B.nat64(B.length(bs)) == Some{body} : Maybe<&2, B.Number64>}
  {body_frame(R.execute(bs, R.Frame{body, ceiling, m})) == B.Number64{0, 0} : B.Number64}
def consumption_integral_exhausts_exactly_o_body(bs, body, ceiling, m, measured):
  match bs:
    case Nil{}:
      Equal.sym(B.Number64, B.Number64{0, 0}, body, F.some_injective(B.Number64, B.Number64{0, 0}, body, measured))
    case Con{+b, +t}:
      +rest = C.decrease64(body)
      +free = C.decrease64(ceiling)
      consumption_integral_exhausts_exactly_o_body(t, rest, free, C.step(m, b, rest, free), length_of_tail_and_decrement_of_body(b, t, body, measured))

law increment_of_predecessor:
  for +n: Nat
  for +w: Word(n)
  {Word.inc(n, predecessor(n, w)) == w : Word(n)}
def increment_of_predecessor(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{True{}, t}:
          {==}
        case WCon{False{}, +t}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r}, Word.inc(p, predecessor(p, t)), t, increment_of_predecessor(p, t))

law subtract_sum_one_cancels:
  for +x: U32
  {((x - 1 : U32) + 1 : U32) == x : U32}
def subtract_sum_one_cancels(x):
  match x:
    case U32{+w}:
      %Equal.sym(Word(32n), Word.sub(32n, w, one(31n)), predecessor(32n, w), subtract_one_decrements(31n, w)) :
        {U32{Word.add(32n, _, one(31n))} == U32{w} : U32}
      %Equal.sym(Word(32n), Word.add(32n, predecessor(32n, w), one(31n)), Word.inc(32n, predecessor(32n, w)), sum_one_increments(31n, predecessor(32n, w))) :
        {U32{_} == U32{w} : U32}
      Equal.cong(Word(32n), U32, r => U32{r}, Word.inc(32n, predecessor(32n, w)), w, increment_of_predecessor(32n, w))

law predecessor_maximum_exactly_in_zero:
  for +n: Nat
  for +w: Word(n)
  {ones(n, predecessor(n, w)) == zeros(n, w) : Bool}
def predecessor_maximum_exactly_in_zero(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{True{}, t}:
          {==}
        case WCon{False{}, t}:
          predecessor_maximum_exactly_in_zero(p, t)

law subtraction_one_maximum_exactly_in_zero:
  for +x: U32
  {U32.is_eq((x - 1 : U32), 4294967295) == U32.is_eq(x, 0) : Bool}
def subtraction_one_maximum_exactly_in_zero(x):
  match x:
    case U32{+w}:
      %Equal.sym(Word(32n), Word.sub(32n, w, one(31n)), predecessor(32n, w), subtract_one_decrements(31n, w)) :
        {Cmp.is_eq(Word.cmp(32n, _, maximum(32n))) == Cmp.is_eq(Word.cmp(32n, w, Word.zero(32n))) : Bool}
      Equal.trans(Bool, Cmp.is_eq(Word.cmp(32n, predecessor(32n, w), maximum(32n))), ones(32n, predecessor(32n, w)), Cmp.is_eq(Word.cmp(32n, w, Word.zero(32n))),
        comparison_maximum_recognizes_bits(32n, predecessor(32n, w)),
        Equal.trans(Bool, ones(32n, predecessor(32n, w)), zeros(32n, w), Cmp.is_eq(Word.cmp(32n, w, Word.zero(32n))), predecessor_maximum_exactly_in_zero(32n, w),
          Equal.sym(Bool, Cmp.is_eq(Word.cmp(32n, w, Word.zero(32n))), zeros(32n, w), comparison_zero_recognizes_bits(32n, w))))

law increase_after_decrease_without_transport:
  for +a: U32
  for +b: U32
  for negative_zero: {U32.is_eq(b, 0) == False{} : Bool}
  {B.increment64(Some{B.Number64{a, (b - 1 : U32)}}) == Some{B.Number64{a, b}} : Maybe<&2, B.Number64>}
def increase_after_decrease_without_transport(a, b, negative_zero):
  %Equal.sym(Bool, U32.is_eq((b - 1 : U32), 4294967295), False{},
    Equal.trans(Bool, U32.is_eq((b - 1 : U32), 4294967295), U32.is_eq(b, 0), False{}, subtraction_one_maximum_exactly_in_zero(b), negative_zero)) :
    {B.increment64_cases(a, (b - 1 : U32), _, U32.is_eq(a, 4294967295)) == Some{B.Number64{a, b}} : Maybe<&2, B.Number64>}
  Equal.cong(U32, Maybe<&2, B.Number64>, r => Some{B.Number64{a, r}}, ((b - 1 : U32) + 1 : U32), b, subtract_sum_one_cancels(b))

law increase_after_decrease_combined_transport:
  for +a: U32
  for negative_zero: {U32.is_eq(a, 0) == False{} : Bool}
  {B.increment64(Some{B.Number64{(a - 1 : U32), 4294967295}}) == Some{B.Number64{a, 0}} : Maybe<&2, B.Number64>}
def increase_after_decrease_combined_transport(a, negative_zero):
  %Equal.sym(Bool, U32.is_eq((a - 1 : U32), 4294967295), False{},
    Equal.trans(Bool, U32.is_eq((a - 1 : U32), 4294967295), U32.is_eq(a, 0), False{}, subtraction_one_maximum_exactly_in_zero(a), negative_zero)) :
    {B.increment64_cases((a - 1 : U32), 4294967295, True{}, _) == Some{B.Number64{a, 0}} : Maybe<&2, B.Number64>}
  Equal.cong(U32, Maybe<&2, B.Number64>, r => Some{B.Number64{r, 0}}, ((a - 1 : U32) + 1 : U32), a, subtract_sum_one_cancels(a))

law zero64_only_recognizes_zero:
  for +n: B.Number64
  for +zero: {C.zero64(n) == True{} : Bool}
  {n == B.Number64{0, 0} : B.Number64}
def zero64_only_recognizes_zero(n, zero):
  match n:
    case B.Number64{+a, +b}:
      %Equal.sym(U32, a, 0, equality_u32(a, 0, F.and_boolean_left(U32.is_eq(a, 0), U32.is_eq(b, 0), zero))) :
        {B.Number64{_, b} == B.Number64{0, 0} : B.Number64}
      Equal.cong(U32, B.Number64, r => B.Number64{0, r}, b, 0,
        equality_u32(b, 0, F.and_boolean_right(U32.is_eq(a, 0), U32.is_eq(b, 0), zero)))

# This helper transports the actual Boolean tests to all three branches
# of decrease64, without treating overflow as silent modular equality.
def invert_decrease_cases(low_zero: Bool, high_zero: Bool, +a: U32, +b: U32,
  eb: {U32.is_eq(b, 0) == low_zero : Bool},
  ea: {U32.is_eq(a, 0) == high_zero : Bool},
  negative_zero: {high_zero && low_zero == False{} : Bool}) ->
  {B.increment64(Some{C.decrease64_cases(low_zero, high_zero, a, b)}) == Some{B.Number64{a, b}} : Maybe<&2, B.Number64>}:
  match low_zero high_zero:
    case False{} _:
      increase_after_decrease_without_transport(a, b, eb)
    case True{} False{}:
      %Equal.sym(U32, b, 0, equality_u32(b, 0, eb)) :
        {B.increment64(Some{B.Number64{(a - 1 : U32), 4294967295}}) == Some{B.Number64{a, _}} : Maybe<&2, B.Number64>}
      increase_after_decrease_combined_transport(a, ea)
    case True{} True{}:
      F.absurd_boolean({B.increment64(Some{B.Number64{0, 0}}) == Some{B.Number64{a, b}} : Maybe<&2, B.Number64>}, Equal.sym(Bool, True{}, False{}, negative_zero))

law increment_inverts_decrease_when_positive:
  for +n: B.Number64
  for negative_zero: {C.zero64(n) == False{} : Bool}
  {B.increment64(Some{C.decrease64(n)}) == Some{n} : Maybe<&2, B.Number64>}
def increment_inverts_decrease_when_positive(n, negative_zero):
  match n:
    case B.Number64{+a, +b}:
      invert_decrease_cases(U32.is_eq(b, 0), U32.is_eq(a, 0), a, b, {==}, {==}, negative_zero)

law decrement_positive_requires_original_positive:
  for +n: B.Number64
  for positive: {C.zero64(C.decrease64(n)) == False{} : Bool}
  {C.zero64(n) == False{} : Bool}
def decrement_positive_requires_original_positive(n, positive):
  false_se_true_impossible(C.zero64(n), e =>
    F.false_negative_true(Equal.sym(Bool, True{}, False{},
      (%zero64_only_recognizes_zero(n, e) : {C.zero64(C.decrease64(_)) == False{} : Bool}
        positive))))

# Exact last/remaining protocol used by emit for both arities.
def last(n: Nat, +q: B.Number64) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n:
      C.one64(q)
    case 2n+p:
      Bool.not(C.one64(q)) && last(1n+p, C.decrease64(q))

law last_accepted_reconstruct_to_count_original:
  for +n: Nat
  for +q: B.Number64
  for +accepted: {last(n, q) == True{} : Bool}
  {B.nat64(n) == Some{q} : Maybe<&2, B.Number64>}
def last_accepted_reconstruct_to_count_original(n, q, accepted):
  match n:
    case 0n:
      F.absurd_boolean({Some{B.Number64{0, 0}} == Some{q} : Maybe<&2, B.Number64>}, accepted)
    case 1n:
      %Equal.sym(B.Number64, q, B.Number64{0, 1}, one64_only_recognizes_one(q, accepted)) :
        {Some{B.Number64{0, 1}} == Some{_} : Maybe<&2, B.Number64>}
      {==}
    case 2n+p:
      +tail = last_accepted_reconstruct_to_count_original(1n+p, C.decrease64(q),
        F.and_boolean_right(Bool.not(C.one64(q)), last(1n+p, C.decrease64(q)), accepted))
      %Equal.sym(Maybe<&2, B.Number64>, B.nat64(1n+p), Some{C.decrease64(q)}, tail) :
        {B.increment64(_) == Some{q} : Maybe<&2, B.Number64>}
      increment_inverts_decrease_when_positive(q,
        decrement_positive_requires_original_positive(q, nat64_successor_never_zero(p, C.decrease64(q), tail)))

law count_representable_complete_o_protocol_of_last:
  for +n: Nat
  for +q: B.Number64
  for +measured: {B.nat64(1n+n) == Some{q} : Maybe<&2, B.Number64>}
  {last(1n+n, q) == True{} : Bool}
def count_representable_complete_o_protocol_of_last(n, q, measured):
  match n:
    case 0n:
      Equal.trans(Bool, C.one64(q), Nat.is_eq(1n, 1n), True{}, one64_reflects_count_natural(1n, q, measured), {==})
    case 1n+p:
      %Equal.sym(Bool, C.one64(q), False{}, one64_reflects_count_natural(2n+p, q, measured)) :
        {Bool.not(_) && last(1n+p, C.decrease64(q)) == True{} : Bool}
      count_representable_complete_o_protocol_of_last(p, C.decrease64(q),
        measure_decremented(1n+p, q, nat64_successor_has_predecessor_exact(1n+p, q, measured)))
