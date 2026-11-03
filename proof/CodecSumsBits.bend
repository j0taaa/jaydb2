# Verified addition for every width: explicit carry and absorbing overflow.
# No width or value limit is used as fuel.
import Base
import ./Foundations.bend as F
import ./CodecCounters.bend as N
import ./CodecWordsWord.bend as W

def end(-n: Nat, overflow: Bool, w: Word(n)) -> Maybe<&2, Word(n)>:
  match overflow:
    case False{}:
      Some{w}
    case True{}:
      None{}

def attach(-n: Nat, b: Bool, m: Maybe<&2, Word(n)>) -> Maybe<&2, Word(1n+n)>:
  match m:
    case None{}:
      None{}
    case Some{w}:
      Some{WCon{b, w}}

def sum(n: Nat, a: Word(n), b: Word(n), c: Bool) -> Maybe<&2, Word(n)>:
  match n:
    case 0n:
      end(0n, c, WNil{})
    case 1n+p:
      match a b c:
        case WCon{False{}, at} WCon{False{}, bt} False{}:
          attach(p, False{}, sum(p, at, bt, False{}))
        case WCon{False{}, at} WCon{False{}, bt} True{}:
          attach(p, True{}, sum(p, at, bt, False{}))
        case WCon{False{}, at} WCon{True{}, bt} False{}:
          attach(p, True{}, sum(p, at, bt, False{}))
        case WCon{False{}, at} WCon{True{}, bt} True{}:
          attach(p, False{}, sum(p, at, bt, True{}))
        case WCon{True{}, at} WCon{False{}, bt} False{}:
          attach(p, True{}, sum(p, at, bt, False{}))
        case WCon{True{}, at} WCon{False{}, bt} True{}:
          attach(p, False{}, sum(p, at, bt, True{}))
        case WCon{True{}, at} WCon{True{}, bt} False{}:
          attach(p, False{}, sum(p, at, bt, True{}))
        case WCon{True{}, at} WCon{True{}, bt} True{}:
          attach(p, True{}, sum(p, at, bt, True{}))

def carry(n: Nat, a: Word(n), b: Word(n), c: Bool) -> Bool:
  match n:
    case 0n:
      c
    case 1n+p:
      match a b c:
        case WCon{False{}, at} WCon{False{}, bt} False{}:
          carry(p, at, bt, False{})
        case WCon{False{}, at} WCon{False{}, bt} True{}:
          carry(p, at, bt, False{})
        case WCon{False{}, at} WCon{True{}, bt} False{}:
          carry(p, at, bt, False{})
        case WCon{False{}, at} WCon{True{}, bt} True{}:
          carry(p, at, bt, True{})
        case WCon{True{}, at} WCon{False{}, bt} False{}:
          carry(p, at, bt, False{})
        case WCon{True{}, at} WCon{False{}, bt} True{}:
          carry(p, at, bt, True{})
        case WCon{True{}, at} WCon{True{}, bt} False{}:
          carry(p, at, bt, True{})
        case WCon{True{}, at} WCon{True{}, bt} True{}:
          carry(p, at, bt, True{})

def increment(+n: Nat, m: Maybe<&2, Word(n)>) -> Maybe<&2, Word(n)>:
  match m:
    case None{}:
      None{}
    case Some{+w}:
      end(n, N.ones(n, w), Word.inc(n, w))

def sum_optional(n: Nat, a: Maybe<&2, Word(n)>, b: Maybe<&2, Word(n)>) -> Maybe<&2, Word(n)>:
  match a b:
    case Some{x} Some{y}:
      sum(n, x, y, False{})
    case _ _:
      None{}

def natural(+n: Nat, v: Nat) -> Maybe<&2, Word(n)>:
  match v:
    case 0n:
      Some{Word.zero(n)}
    case 1n+p:
      increment(n, natural(n, p))

law attach_end:
  for +n: Nat
  for +b: Bool
  for +c: Bool
  for +w: Word(n)
  {attach(n, b, end(n, c, w)) == end(1n+n, c, WCon{b, w}) : Maybe<&2, Word(1n+n)>}
def attach_end(n, b, c, w):
  match c:
    case False{}:
      {==}
    case True{}:
      {==}

# One induction step: appending the computed bit preserves the exact result.
def attach_result_exact(+n: Nat, +b: Bool, +m: Maybe<&2, Word(n)>,
  +c: Bool, +w: Word(n), exact: {m == end(n, c, w) : Maybe<&2, Word(n)>}) ->
  {attach(n, b, m) == end(1n+n, c, WCon{b, w}) : Maybe<&2, Word(1n+n)>}:
  Equal.trans(Maybe<&2, Word(1n+n)>,
    attach(n, b, m), attach(n, b, end(n, c, w)), end(1n+n, c, WCon{b, w}),
    Equal.cong(Maybe<&2, Word(n)>, Maybe<&2, Word(1n+n)>, m => attach(n, b, m),
      m, end(n, c, w), exact),
    attach_end(n, b, c, w))

law sum_exact:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +c: Bool
  {sum(n, a, b, c) == end(n, carry(n, a, b, c), Word.adc(n, a, b, False{}, c)) : Maybe<&2, Word(n)>}
def sum_exact(n, a, b, c):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b c:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          attach_result_exact(p, False{}, sum(p, at, bt, False{}),
            carry(p, at, bt, False{}), Word.adc(p, at, bt, False{}, False{}), sum_exact(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          attach_result_exact(p, True{}, sum(p, at, bt, False{}),
            carry(p, at, bt, False{}), Word.adc(p, at, bt, False{}, False{}), sum_exact(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          attach_result_exact(p, True{}, sum(p, at, bt, False{}),
            carry(p, at, bt, False{}), Word.adc(p, at, bt, False{}, False{}), sum_exact(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          attach_result_exact(p, False{}, sum(p, at, bt, True{}),
            carry(p, at, bt, True{}), Word.adc(p, at, bt, False{}, True{}), sum_exact(p, at, bt, True{}))
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          attach_result_exact(p, True{}, sum(p, at, bt, False{}),
            carry(p, at, bt, False{}), Word.adc(p, at, bt, False{}, False{}), sum_exact(p, at, bt, False{}))
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          attach_result_exact(p, False{}, sum(p, at, bt, True{}),
            carry(p, at, bt, True{}), Word.adc(p, at, bt, False{}, True{}), sum_exact(p, at, bt, True{}))
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          attach_result_exact(p, False{}, sum(p, at, bt, True{}),
            carry(p, at, bt, True{}), Word.adc(p, at, bt, False{}, True{}), sum_exact(p, at, bt, True{}))
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          attach_result_exact(p, True{}, sum(p, at, bt, True{}),
            carry(p, at, bt, True{}), Word.adc(p, at, bt, False{}, True{}), sum_exact(p, at, bt, True{}))

law increment_attach_zero:
  for +n: Nat
  for +m: Maybe<&2, Word(n)>
  {increment(1n+n, attach(n, False{}, m)) == attach(n, True{}, m) : Maybe<&2, Word(1n+n)>}
def increment_attach_zero(n, m):
  match m:
    case None{}:
      {==}
    case Some{w}:
      {==}

law increment_attach_one:
  for +n: Nat
  for +m: Maybe<&2, Word(n)>
  {increment(1n+n, attach(n, True{}, m)) == attach(n, False{}, increment(n, m)) : Maybe<&2, Word(1n+n)>}
def increment_attach_one(n, m):
  match m:
    case None{}:
      {==}
    case Some{+w}:
      Equal.sym(Maybe<&2, Word(1n+n)>,
        attach(n, False{}, end(n, N.ones(n, w), Word.inc(n, w))),
        end(1n+n, N.ones(n, w), WCon{False{}, Word.inc(n, w)}),
        attach_end(n, False{}, N.ones(n, w), Word.inc(n, w)))

law carry_initial_and_increment:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  {sum(n, a, b, True{}) == increment(n, sum(n, a, b, False{})) : Maybe<&2, Word(n)>}
def carry_initial_and_increment(n, a, b):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          Equal.sym(Maybe<&2, Word(1n+p)>, increment(1n+p, attach(p, False{}, sum(p, at, bt, False{}))), attach(p, True{}, sum(p, at, bt, False{})),
            increment_attach_zero(p, sum(p, at, bt, False{})))
        case WCon{False{}, +at} WCon{True{}, +bt}:
          Equal.trans(Maybe<&2, Word(1n+p)>,
            attach(p, False{}, sum(p, at, bt, True{})), attach(p, False{}, increment(p, sum(p, at, bt, False{}))),
            increment(1n+p, attach(p, True{}, sum(p, at, bt, False{}))),
            Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => attach(p, False{}, m),
              sum(p, at, bt, True{}), increment(p, sum(p, at, bt, False{})), carry_initial_and_increment(p, at, bt)),
            Equal.sym(Maybe<&2, Word(1n+p)>, increment(1n+p, attach(p, True{}, sum(p, at, bt, False{}))), attach(p, False{}, increment(p, sum(p, at, bt, False{}))),
              increment_attach_one(p, sum(p, at, bt, False{}))))
        case WCon{True{}, +at} WCon{False{}, +bt}:
          Equal.trans(Maybe<&2, Word(1n+p)>,
            attach(p, False{}, sum(p, at, bt, True{})), attach(p, False{}, increment(p, sum(p, at, bt, False{}))),
            increment(1n+p, attach(p, True{}, sum(p, at, bt, False{}))),
            Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => attach(p, False{}, m),
              sum(p, at, bt, True{}), increment(p, sum(p, at, bt, False{})), carry_initial_and_increment(p, at, bt)),
            Equal.sym(Maybe<&2, Word(1n+p)>, increment(1n+p, attach(p, True{}, sum(p, at, bt, False{}))), attach(p, False{}, increment(p, sum(p, at, bt, False{}))),
              increment_attach_one(p, sum(p, at, bt, False{}))))
        case WCon{True{}, +at} WCon{True{}, +bt}:
          Equal.sym(Maybe<&2, Word(1n+p)>, increment(1n+p, attach(p, False{}, sum(p, at, bt, True{}))), attach(p, True{}, sum(p, at, bt, True{})),
            increment_attach_zero(p, sum(p, at, bt, True{})))

law increment_argument_without_overflow:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for fits: {N.ones(n, a) == False{} : Bool}
  {sum(n, Word.inc(n, a), b, False{}) == sum(n, a, b, True{}) : Maybe<&2, Word(n)>}
def increment_argument_without_overflow(n, a, b, fits):
  match n:
    case 0n:
      F.absurd_boolean({sum(0n, Word.inc(0n, a), b, False{}) == sum(0n, a, b, True{}) : Maybe<&2, Word(0n)>}, Equal.sym(Bool, True{}, False{}, fits))
    case 1n+p:
      match a b:
        case WCon{False{}, at} WCon{False{}, bt}:
          {==}
        case WCon{False{}, at} WCon{True{}, bt}:
          {==}
        case WCon{True{}, +at} WCon{False{}, +bt}:
          Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => attach(p, False{}, m),
            sum(p, Word.inc(p, at), bt, False{}), sum(p, at, bt, True{}), increment_argument_without_overflow(p, at, bt, fits))
        case WCon{True{}, +at} WCon{True{}, +bt}:
          Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => attach(p, True{}, m),
            sum(p, Word.inc(p, at), bt, False{}), sum(p, at, bt, True{}), increment_argument_without_overflow(p, at, bt, fits))

law maximum_combined_carry_overflows:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for maximum: {N.ones(n, a) == True{} : Bool}
  {sum(n, a, b, True{}) == None{} : Maybe<&2, Word(n)>}
def maximum_combined_carry_overflows(n, a, b, maximum):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a b:
        case WCon{False{}, at} WCon{y, bt}:
          F.absurd_boolean({sum(1n+p, WCon{False{}, at}, WCon{y, bt}, True{}) == None{} : Maybe<&2, Word(1n+p)>}, maximum)
        case WCon{True{}, +at} WCon{False{}, +bt}:
          Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => attach(p, False{}, m),
            sum(p, at, bt, True{}), None{}, maximum_combined_carry_overflows(p, at, bt, maximum))
        case WCon{True{}, +at} WCon{True{}, +bt}:
          Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => attach(p, True{}, m),
            sum(p, at, bt, True{}), None{}, maximum_combined_carry_overflows(p, at, bt, maximum))

def sum_increment_cases(maximum: Bool, +n: Nat, +a: Word(n), +b: Word(n),
  e: {N.ones(n, a) == maximum : Bool}) ->
  {sum_optional(n, end(n, maximum, Word.inc(n, a)), Some{b}) == increment(n, sum(n, a, b, False{})) : Maybe<&2, Word(n)>}:
  match maximum:
    case False{}:
      Equal.trans(Maybe<&2, Word(n)>, sum(n, Word.inc(n, a), b, False{}), sum(n, a, b, True{}), increment(n, sum(n, a, b, False{})),
        increment_argument_without_overflow(n, a, b, e), carry_initial_and_increment(n, a, b))
    case True{}:
      Equal.sym(Maybe<&2, Word(n)>, increment(n, sum(n, a, b, False{})), None{},
        Equal.trans(Maybe<&2, Word(n)>, increment(n, sum(n, a, b, False{})), sum(n, a, b, True{}), None{},
          Equal.sym(Maybe<&2, Word(n)>, sum(n, a, b, True{}), increment(n, sum(n, a, b, False{})), carry_initial_and_increment(n, a, b)),
          maximum_combined_carry_overflows(n, a, b, e)))

law sum_none_right:
  for n: Nat
  for a: Maybe<&2, Word(n)>
  {sum_optional(n, a, None{}) == None{} : Maybe<&2, Word(n)>}
def sum_none_right(n, a):
  match a:
    case None{}:
      {==}
    case Some{x}:
      {==}

law sum_optional_preserves_increment:
  for +n: Nat
  for +a: Maybe<&2, Word(n)>
  for +b: Maybe<&2, Word(n)>
  {sum_optional(n, increment(n, a), b) == increment(n, sum_optional(n, a, b)) : Maybe<&2, Word(n)>}
def sum_optional_preserves_increment(n, a, b):
  match a b:
    case None{} _:
      {==}
    case Some{+x} None{}:
      sum_none_right(n, increment(n, Some{x}))
    case Some{+x} Some{+y}:
      sum_increment_cases(N.ones(n, x), n, x, y, {==})

law sum_zero:
  for +n: Nat
  for +a: Word(n)
  {sum(n, Word.zero(n), a, False{}) == Some{a} : Maybe<&2, Word(n)>}
def sum_zero(n, a):
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{False{}, +t}:
          Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => attach(p, False{}, m),
            sum(p, Word.zero(p), t, False{}), Some{t}, sum_zero(p, t))
        case WCon{True{}, +t}:
          Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => attach(p, True{}, m),
            sum(p, Word.zero(p), t, False{}), Some{t}, sum_zero(p, t))

law sum_optional_zero:
  for +n: Nat
  for +a: Maybe<&2, Word(n)>
  {sum_optional(n, Some{Word.zero(n)}, a) == a : Maybe<&2, Word(n)>}
def sum_optional_zero(n, a):
  match a:
    case None{}:
      {==}
    case Some{+w}:
      sum_zero(n, w)

# TOTAL homomorphism: also covers unrepresentable operands and results.
law sum_naturals:
  for +width: Nat
  for +a: Nat
  for +b: Nat
  {sum_optional(width, natural(width, a), natural(width, b)) == natural(width, Nat.add(a, b)) : Maybe<&2, Word(width)>}
def sum_naturals(width, a, b):
  match a:
    case 0n:
      sum_optional_zero(width, natural(width, b))
    case 1n+p:
      Equal.trans(Maybe<&2, Word(width)>,
        sum_optional(width, increment(width, natural(width, p)), natural(width, b)),
        increment(width, sum_optional(width, natural(width, p), natural(width, b))),
        increment(width, natural(width, Nat.add(p, b))),
        sum_optional_preserves_increment(width, natural(width, p), natural(width, b)),
        Equal.cong(Maybe<&2, Word(width)>, Maybe<&2, Word(width)>, m => increment(width, m),
          sum_optional(width, natural(width, p), natural(width, b)), natural(width, Nat.add(p, b)), sum_naturals(width, p, b)))

# The carry of a+b is exactly the modular drop below a.
# With input carry, equality with a also signals overflow.
def test(c: Bool, order: Cmp) -> Bool:
  match c:
    case False{}:
      Cmp.is_lt(order)
    case True{}:
      Cmp.is_le(order)

def first(pair: Bool & Bool) -> Bool:
  (s, k) = pair
  s

def second(pair: Bool & Bool) -> Bool:
  (s, k) = pair
  k

def bit_sum(a: Bool, b: Bool, c: Bool) -> Bool:
  first(Bool.full_add(a, b, c))

def bit_carry(a: Bool, b: Bool, c: Bool) -> Bool:
  second(Bool.full_add(a, b, c))

law test_bit:
  for a: Bool
  for b: Bool
  for c: Bool
  for t: Cmp
  {test(c, Word.cmp.fin(bit_sum(a, b, c), a, t)) == test(bit_carry(a, b, c), t) : Bool}
def test_bit(a, b, c, t):
  match a b c t:
    case False{} False{} False{} LT{}:
      {==}
    case False{} False{} False{} EQ{}:
      {==}
    case False{} False{} False{} GT{}:
      {==}
    case False{} False{} True{} LT{}:
      {==}
    case False{} False{} True{} EQ{}:
      {==}
    case False{} False{} True{} GT{}:
      {==}
    case False{} True{} False{} LT{}:
      {==}
    case False{} True{} False{} EQ{}:
      {==}
    case False{} True{} False{} GT{}:
      {==}
    case False{} True{} True{} LT{}:
      {==}
    case False{} True{} True{} EQ{}:
      {==}
    case False{} True{} True{} GT{}:
      {==}
    case True{} False{} False{} LT{}:
      {==}
    case True{} False{} False{} EQ{}:
      {==}
    case True{} False{} False{} GT{}:
      {==}
    case True{} False{} True{} LT{}:
      {==}
    case True{} False{} True{} EQ{}:
      {==}
    case True{} False{} True{} GT{}:
      {==}
    case True{} True{} False{} LT{}:
      {==}
    case True{} True{} False{} EQ{}:
      {==}
    case True{} True{} False{} GT{}:
      {==}
    case True{} True{} True{} LT{}:
      {==}
    case True{} True{} True{} EQ{}:
      {==}
    case True{} True{} True{} GT{}:
      {==}

# The one-bit table transports the tail comparison to the whole word.
def transport_test_bit(+a: Bool, +b: Bool, +c: Bool, +t: Cmp, +r: Bool,
  tail: {r == test(bit_carry(a, b, c), t) : Bool}) ->
  {r == test(c, Word.cmp.fin(bit_sum(a, b, c), a, t)) : Bool}:
  Equal.trans(Bool, r, test(bit_carry(a, b, c), t),
    test(c, Word.cmp.fin(bit_sum(a, b, c), a, t)), tail,
    Equal.sym(Bool, test(c, Word.cmp.fin(bit_sum(a, b, c), a, t)),
      test(bit_carry(a, b, c), t), test_bit(a, b, c, t)))

law carry_equivalent_comparison:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for +c: Bool
  {carry(n, a, b, c) == test(c, Word.cmp(n, Word.adc(n, a, b, False{}, c), a)) : Bool}
def carry_equivalent_comparison(n, a, b, c):
  match n:
    case 0n:
      match c:
        case False{}:
          {==}
        case True{}:
          {==}
    case 1n+p:
      match a b c:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          transport_test_bit(False{}, False{}, False{},
            Word.cmp(p, Word.adc(p, at, bt, False{}, False{}), at),
            carry(p, at, bt, False{}), carry_equivalent_comparison(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          transport_test_bit(False{}, False{}, True{},
            Word.cmp(p, Word.adc(p, at, bt, False{}, False{}), at),
            carry(p, at, bt, False{}), carry_equivalent_comparison(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          transport_test_bit(False{}, True{}, False{},
            Word.cmp(p, Word.adc(p, at, bt, False{}, False{}), at),
            carry(p, at, bt, False{}), carry_equivalent_comparison(p, at, bt, False{}))
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          transport_test_bit(False{}, True{}, True{},
            Word.cmp(p, Word.adc(p, at, bt, False{}, True{}), at),
            carry(p, at, bt, True{}), carry_equivalent_comparison(p, at, bt, True{}))
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          transport_test_bit(True{}, False{}, False{},
            Word.cmp(p, Word.adc(p, at, bt, False{}, False{}), at),
            carry(p, at, bt, False{}), carry_equivalent_comparison(p, at, bt, False{}))
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          transport_test_bit(True{}, False{}, True{},
            Word.cmp(p, Word.adc(p, at, bt, False{}, True{}), at),
            carry(p, at, bt, True{}), carry_equivalent_comparison(p, at, bt, True{}))
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          transport_test_bit(True{}, True{}, False{},
            Word.cmp(p, Word.adc(p, at, bt, False{}, True{}), at),
            carry(p, at, bt, True{}), carry_equivalent_comparison(p, at, bt, True{}))
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          transport_test_bit(True{}, True{}, True{},
            Word.cmp(p, Word.adc(p, at, bt, False{}, True{}), at),
            carry(p, at, bt, True{}), carry_equivalent_comparison(p, at, bt, True{}))

def join_optional(+k: Nat, -n: Nat, lo: Word(k), m: Maybe<&2, Word(n)>) -> Maybe<&2, Word(Nat.add(k, n))>:
  match m:
    case None{}:
      None{}
    case Some{hi}:
      Some{W.join(k, n, lo, hi)}

law join_optional_zero:
  for n: Nat
  for lo: Word(0n)
  for m: Maybe<&2, Word(n)>
  {join_optional(0n, n, lo, m) == m : Maybe<&2, Word(n)>}
def join_optional_zero(n, lo, m):
  match m:
    case None{}:
      {==}
    case Some{hi}:
      {==}

law attach_join:
  for +k: Nat
  for n: Nat
  for +b: Bool
  for +lo: Word(k)
  for +m: Maybe<&2, Word(n)>
  {attach(Nat.add(k, n), b, join_optional(k, n, lo, m)) == join_optional(1n+k, n, WCon{b, lo}, m) : Maybe<&2, Word(1n+Nat.add(k, n))>}
def attach_join(k, n, b, lo, m):
  match m:
    case None{}:
      {==}
    case Some{hi}:
      {==}

# The same append step for low/high block decomposition.
def attach_result_blocks(+k: Nat, +n: Nat, +b: Bool,
  +m: Maybe<&2, Word(Nat.add(k, n))>, +lo: Word(k), +hi: Maybe<&2, Word(n)>,
  blocks: {m == join_optional(k, n, lo, hi) : Maybe<&2, Word(Nat.add(k, n))>}) ->
  {attach(Nat.add(k, n), b, m) == join_optional(1n+k, n, WCon{b, lo}, hi) : Maybe<&2, Word(1n+Nat.add(k, n))>}:
  Equal.trans(Maybe<&2, Word(1n+Nat.add(k, n))>,
    attach(Nat.add(k, n), b, m), attach(Nat.add(k, n), b, join_optional(k, n, lo, hi)),
    join_optional(1n+k, n, WCon{b, lo}, hi),
    Equal.cong(Maybe<&2, Word(Nat.add(k, n))>, Maybe<&2, Word(1n+Nat.add(k, n))>,
      m => attach(Nat.add(k, n), b, m), m, join_optional(k, n, lo, hi), blocks),
    attach_join(k, n, b, lo, hi))

law sum_blocks:
  for +k: Nat
  for +n: Nat
  for +al: Word(k)
  for +bl: Word(k)
  for +ah: Word(n)
  for +bh: Word(n)
  for +c: Bool
  {sum(Nat.add(k, n), W.join(k, n, al, ah), W.join(k, n, bl, bh), c) ==
    join_optional(k, n, Word.adc(k, al, bl, False{}, c), sum(n, ah, bh, carry(k, al, bl, c))) : Maybe<&2, Word(Nat.add(k, n))>}
def sum_blocks(k, n, al, bl, ah, bh, c):
  match k:
    case 0n:
      Equal.sym(Maybe<&2, Word(n)>, join_optional(0n, n, WNil{}, sum(n, ah, bh, c)), sum(n, ah, bh, c),
        join_optional_zero(n, WNil{}, sum(n, ah, bh, c)))
    case 1n+p:
      match al bl c:
        case WCon{False{}, +at} WCon{False{}, +bt} False{}:
          attach_result_blocks(p, n, False{},
            sum(Nat.add(p, n), W.join(p, n, at, ah), W.join(p, n, bt, bh), False{}),
            Word.adc(p, at, bt, False{}, False{}), sum(n, ah, bh, carry(p, at, bt, False{})),
            sum_blocks(p, n, at, bt, ah, bh, False{}))
        case WCon{False{}, +at} WCon{False{}, +bt} True{}:
          attach_result_blocks(p, n, True{},
            sum(Nat.add(p, n), W.join(p, n, at, ah), W.join(p, n, bt, bh), False{}),
            Word.adc(p, at, bt, False{}, False{}), sum(n, ah, bh, carry(p, at, bt, False{})),
            sum_blocks(p, n, at, bt, ah, bh, False{}))
        case WCon{False{}, +at} WCon{True{}, +bt} False{}:
          attach_result_blocks(p, n, True{},
            sum(Nat.add(p, n), W.join(p, n, at, ah), W.join(p, n, bt, bh), False{}),
            Word.adc(p, at, bt, False{}, False{}), sum(n, ah, bh, carry(p, at, bt, False{})),
            sum_blocks(p, n, at, bt, ah, bh, False{}))
        case WCon{False{}, +at} WCon{True{}, +bt} True{}:
          attach_result_blocks(p, n, False{},
            sum(Nat.add(p, n), W.join(p, n, at, ah), W.join(p, n, bt, bh), True{}),
            Word.adc(p, at, bt, False{}, True{}), sum(n, ah, bh, carry(p, at, bt, True{})),
            sum_blocks(p, n, at, bt, ah, bh, True{}))
        case WCon{True{}, +at} WCon{False{}, +bt} False{}:
          attach_result_blocks(p, n, True{},
            sum(Nat.add(p, n), W.join(p, n, at, ah), W.join(p, n, bt, bh), False{}),
            Word.adc(p, at, bt, False{}, False{}), sum(n, ah, bh, carry(p, at, bt, False{})),
            sum_blocks(p, n, at, bt, ah, bh, False{}))
        case WCon{True{}, +at} WCon{False{}, +bt} True{}:
          attach_result_blocks(p, n, False{},
            sum(Nat.add(p, n), W.join(p, n, at, ah), W.join(p, n, bt, bh), True{}),
            Word.adc(p, at, bt, False{}, True{}), sum(n, ah, bh, carry(p, at, bt, True{})),
            sum_blocks(p, n, at, bt, ah, bh, True{}))
        case WCon{True{}, +at} WCon{True{}, +bt} False{}:
          attach_result_blocks(p, n, False{},
            sum(Nat.add(p, n), W.join(p, n, at, ah), W.join(p, n, bt, bh), True{}),
            Word.adc(p, at, bt, False{}, True{}), sum(n, ah, bh, carry(p, at, bt, True{})),
            sum_blocks(p, n, at, bt, ah, bh, True{}))
        case WCon{True{}, +at} WCon{True{}, +bt} True{}:
          attach_result_blocks(p, n, True{},
            sum(Nat.add(p, n), W.join(p, n, at, ah), W.join(p, n, bt, bh), True{}),
            Word.adc(p, at, bt, False{}, True{}), sum(n, ah, bh, carry(p, at, bt, True{})),
            sum_blocks(p, n, at, bt, ah, bh, True{}))

law sum_zero_right:
  for +n: Nat
  for +a: Word(n)
  {sum(n, a, Word.zero(n), False{}) == Some{a} : Maybe<&2, Word(n)>}
def sum_zero_right(n, a):
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{False{}, +t}:
          Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => attach(p, False{}, m),
            sum(p, t, Word.zero(p), False{}), Some{t}, sum_zero_right(p, t))
        case WCon{True{}, +t}:
          Equal.cong(Maybe<&2, Word(p)>, Maybe<&2, Word(1n+p)>, m => attach(p, True{}, m),
            sum(p, t, Word.zero(p), False{}), Some{t}, sum_zero_right(p, t))

law sum_increment:
  for +n: Nat
  for +a: Word(n)
  {sum(n, a, Word.zero(n), True{}) == increment(n, Some{a}) : Maybe<&2, Word(n)>}
def sum_increment(n, a):
  Equal.trans(Maybe<&2, Word(n)>, sum(n, a, Word.zero(n), True{}), increment(n, sum(n, a, Word.zero(n), False{})), increment(n, Some{a}),
    carry_initial_and_increment(n, a, Word.zero(n)),
    Equal.cong(Maybe<&2, Word(n)>, Maybe<&2, Word(n)>, m => increment(n, m), sum(n, a, Word.zero(n), False{}), Some{a}, sum_zero_right(n, a)))

law carry_zero:
  for +n: Nat
  for +a: Word(n)
  {carry(n, a, Word.zero(n), False{}) == False{} : Bool}
def carry_zero(n, a):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a:
        case WCon{False{}, t}:
          carry_zero(p, t)
        case WCon{True{}, t}:
          carry_zero(p, t)

law carry_increment:
  for +n: Nat
  for +a: Word(n)
  {carry(n, a, Word.zero(n), True{}) == N.ones(n, a) : Bool}
def carry_increment(n, a):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a:
        case WCon{False{}, t}:
          carry_zero(p, t)
        case WCon{True{}, t}:
          carry_increment(p, t)

law increment_maximum_zero:
  for +n: Nat
  for +a: Word(n)
  for maximum: {N.ones(n, a) == True{} : Bool}
  {Word.inc(n, a) == Word.zero(n) : Word(n)}
def increment_maximum_zero(n, a, maximum):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match a:
        case WCon{False{}, t}:
          F.absurd_boolean({Word.inc(1n+p, WCon{False{}, t}) == Word.zero(1n+p) : Word(1n+p)}, maximum)
        case WCon{True{}, +t}:
          Equal.cong(Word(p), Word(1n+p), w => WCon{False{}, w}, Word.inc(p, t), Word.zero(p), increment_maximum_zero(p, t, maximum))
