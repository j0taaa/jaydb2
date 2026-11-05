# Exact two's-complement words; checked signed overflow, never native Nat64.
import Base
import ./Value.bend as V

def negative(x: V.Int64) -> Bool:
  V.Int64{h, l} = x
  U32.is_ge(h, 2147483648)

def eq(a: V.Int64, b: V.Int64) -> Bool:
  V.Int64{h, l} = a
  V.Int64{i, j} = b
  U32.is_eq(h, i) && U32.is_eq(l, j)

def lt(a: V.Int64, b: V.Int64) -> Bool:
  V.Int64{+h, l} = a
  V.Int64{+i, j} = b
  # Flipping the sign bit maps signed order to unsigned lexicographic order.
  U32.is_lt(U32.xor(h, 2147483648), U32.xor(i, 2147483648)) ||
    (U32.is_eq(h, i) && U32.is_lt(l, j))

def wrapping_add(a: V.Int64, b: V.Int64) -> V.Int64:
  V.Int64{h, +l} = a
  V.Int64{i, j} = b
  +low = U32.add(l, j)
  V.Int64{U32.add(U32.add(h, i), Bool.to_u32(U32.is_lt(low, l))), low}

def wrapping_sub(a: V.Int64, b: V.Int64) -> V.Int64:
  V.Int64{h, +l} = a
  V.Int64{i, +j} = b
  V.Int64{U32.sub(U32.sub(h, i), Bool.to_u32(U32.is_lt(l, j))), U32.sub(l, j)}

def checked(overflow: Bool, result: V.Int64) -> Maybe<&2, V.Int64>:
  match overflow:
    case True{}: None{}
    case False{}: Some{result}

def add_overflow(+a: V.Int64, +b: V.Int64) -> Bool:
  Bool.not(Bool.xor(negative(a), negative(b))) && Bool.xor(negative(a), negative(wrapping_add(a, b)))

def sub_overflow(+a: V.Int64, +b: V.Int64) -> Bool:
  Bool.xor(negative(a), negative(b)) && Bool.xor(negative(a), negative(wrapping_sub(a, b)))

def add(+a: V.Int64, +b: V.Int64) -> Maybe<&2, V.Int64>:
  checked(add_overflow(a, b), wrapping_add(a, b))

def sub(+a: V.Int64, +b: V.Int64) -> Maybe<&2, V.Int64>:
  checked(sub_overflow(a, b), wrapping_sub(a, b))

def increment(x: V.Int64) -> Maybe<&2, V.Int64>:
  add(x, V.Int64{0, 1})

def decrement(x: V.Int64) -> Maybe<&2, V.Int64>:
  sub(x, V.Int64{0, 1})

# A general functional guarantee: every accepted addition returns exactly the
# two-word result and satisfies the signed overflow predicate, for ALL words.
def Matches(result: Maybe<&2, V.Int64>, expected: V.Int64) -> Type:
  match result:
    case None{}: Unit
    case Some{x}: {x == expected : V.Int64}

law checked_result:
  for overflow: Bool
  for +value: V.Int64
  Matches(checked(overflow, value), value)
def checked_result(overflow, value):
  match overflow:
    case False{}: {==}
    case True{}: Unit{}

law accepted_add:
  for +a: V.Int64
  for +b: V.Int64
  Matches(add(a, b), wrapping_add(a, b))
def accepted_add(a, b):
  checked_result(Bool.not(Bool.xor(negative(a), negative(b))) && Bool.xor(negative(a), negative(wrapping_add(a, b))), wrapping_add(a, b))

# Unsigned magnitude helpers, still two words (including abs(INT64_MIN)).
def zero(x: V.Int64) -> Bool:
  V.Int64{h, l} = x
  U32.is_zero(h) && U32.is_zero(l)

def unsigned_lt(a: V.Int64, b: V.Int64) -> Bool:
  V.Int64{+h, l} = a
  V.Int64{+i, j} = b
  U32.is_lt(h, i) || (U32.is_eq(h, i) && U32.is_lt(l, j))

def shl(x: V.Int64) -> V.Int64:
  V.Int64{h, +l} = x
  V.Int64{U32.or(U32.shl(h), Bool.to_u32(U32.is_ge(l, 2147483648))), U32.shl(l)}

# U32.shr is a one-bit shift. Carry the low bit of high into bit31 of low.
def shr(x: V.Int64) -> V.Int64:
  V.Int64{+h, l} = x
  V.Int64{U32.shr(h), U32.or(U32.shr(l), U32.mul(U32.and(h, 1), 2147483648))}

def odd(x: V.Int64) -> Bool:
  V.Int64{h, l} = x
  U32.is_eq(U32.and(l, 1), 1)

def magnitude(+x: V.Int64) -> V.Int64:
  Bool.pick(V.Int64, negative(x), wrapping_sub(V.Int64{0, 0}, x), x)

def signed_word(neg: Bool, +x: V.Int64) -> V.Int64:
  Bool.pick(V.Int64, neg, wrapping_sub(V.Int64{0, 0}, x), x)

def out_of_range(neg: Bool, +x: V.Int64) -> Bool:
  Bool.pick(Bool, neg, unsigned_lt(V.Int64{2147483648, 0}, x), negative(x))

def signed(+neg: Bool, +x: V.Int64) -> Maybe<&2, V.Int64>:
  checked(out_of_range(neg, x), signed_word(neg, x))

def continue_unsigned(overflow: Bool, next: Unit -> Maybe<&2, V.Int64>) -> Maybe<&2, V.Int64>:
  match overflow:
    case True{}: None{}
    case False{}: next(Unit{})

def multiply_step(n: Nat, +a: V.Int64, +b: V.Int64, +acc: V.Int64) -> Maybe<&2, V.Int64>:
  match n:
    case Zero{}: Some{acc}
    case Succ{m}:
      +tail = shr(b)
      +added = wrapping_add(acc, a)
      +result = Bool.pick(V.Int64, odd(b), added, acc)
      continue_unsigned((odd(b) && unsigned_lt(added, acc)) || (negative(a) && Bool.not(zero(tail))),
        u => multiply_step(m, shl(a), tail, result))

def sign_result(neg: Bool, result: Maybe<&2, V.Int64>) -> Maybe<&2, V.Int64>:
  match result:
    case None{}: None{}
    case Some{x}: signed(neg, x)

def mul(+a: V.Int64, +b: V.Int64) -> Maybe<&2, V.Int64>:
  sign_result(Bool.xor(negative(a), negative(b)), multiply_step(64n, magnitude(a), magnitude(b), V.Int64{0, 0}))

type Division is Data:
  Division{quotient: V.Int64, remainder: V.Int64}

# Restoring unsigned division. Inputs are magnitudes <= 2^63; remainder<d,
# so its shift fits 64 bits. Nat is only the small loop index (64).
def divide_step(n: Nat, +input: V.Int64, +d: V.Int64, q: V.Int64, r: V.Int64) -> Division:
  match n:
    case Zero{}: Division{q, r}
    case Succ{m}:
      +next_r = wrapping_add(shl(r), V.Int64{0, Bool.to_u32(negative(input))})
      +subtract = Bool.not(unsigned_lt(next_r, d))
      divide_step(m, shl(input), d,
        wrapping_add(shl(q), V.Int64{0, Bool.to_u32(subtract)}),
        Bool.pick(V.Int64, subtract, wrapping_sub(next_r, d), next_r))

def division_quotient(q: Maybe<&2, V.Int64>, r: V.Int64) -> Maybe<&2, Division>:
  match q:
    case None{}: None{}
    case Some{x}: Some{Division{x, r}}


def signed_division(neg_q: Bool, neg_r: Bool, result: Division) -> Maybe<&2, Division>:
  Division{q, +r} = result
  division_quotient(signed(neg_q, q), Bool.pick(V.Int64, neg_r, wrapping_sub(V.Int64{0, 0}, r), r))

def divide_nonzero(is_zero: Bool, +a: V.Int64, +b: V.Int64) -> Maybe<&2, Division>:
  match is_zero:
    case True{}: None{}
    case False{}: signed_division(Bool.xor(negative(a), negative(b)), negative(a),
      divide_step(64n, magnitude(a), magnitude(b), V.Int64{0, 0}, V.Int64{0, 0}))

# Truncates toward zero; remainder has dividend's sign. Rejects zero divisor
# and INT64_MIN/-1, so quotient/remainder always fit stored signed64.
def divmod(+a: V.Int64, +b: V.Int64) -> Maybe<&2, Division>:
  divide_nonzero(zero(b), a, b)

# These two-sided equations include a success obligation. In particular an
# always-None implementation CANNOT satisfy success_under_no_overflow.
law checked_success:
  for +overflow: Bool
  for +value: V.Int64
  for h: {overflow == False{} : Bool}
  {checked(overflow, value) == Some{value} : Maybe<&2, V.Int64>}
def checked_success(overflow, value, h):
  %Equal.sym(Bool, overflow, False{}, h) : {checked(_, value) == Some{value} : Maybe<&2, V.Int64>}
  {==}

law checked_rejected:
  for +overflow: Bool
  for +value: V.Int64
  for h: {overflow == True{} : Bool}
  {checked(overflow, value) == None{} : Maybe<&2, V.Int64>}
def checked_rejected(overflow, value, h):
  %Equal.sym(Bool, overflow, True{}, h) : {checked(_, value) == None{} : Maybe<&2, V.Int64>}
  {==}

law add_success_under_no_overflow:
  for +a: V.Int64
  for +b: V.Int64
  for h: {add_overflow(a, b) == False{} : Bool}
  {add(a, b) == Some{wrapping_add(a, b)} : Maybe<&2, V.Int64>}
def add_success_under_no_overflow(a, b, h):
  checked_success(add_overflow(a, b), wrapping_add(a, b), h)

law add_rejects_overflow:
  for +a: V.Int64
  for +b: V.Int64
  for h: {add_overflow(a, b) == True{} : Bool}
  {add(a, b) == None{} : Maybe<&2, V.Int64>}
def add_rejects_overflow(a, b, h):
  checked_rejected(add_overflow(a, b), wrapping_add(a, b), h)

law sub_success_under_no_overflow:
  for +a: V.Int64
  for +b: V.Int64
  for h: {sub_overflow(a, b) == False{} : Bool}
  {sub(a, b) == Some{wrapping_sub(a, b)} : Maybe<&2, V.Int64>}
def sub_success_under_no_overflow(a, b, h):
  checked_success(sub_overflow(a, b), wrapping_sub(a, b), h)

law sub_rejects_overflow:
  for +a: V.Int64
  for +b: V.Int64
  for h: {sub_overflow(a, b) == True{} : Bool}
  {sub(a, b) == None{} : Maybe<&2, V.Int64>}
def sub_rejects_overflow(a, b, h):
  checked_rejected(sub_overflow(a, b), wrapping_sub(a, b), h)

law signed_success:
  for +neg: Bool
  for +x: V.Int64
  for h: {out_of_range(neg, x) == False{} : Bool}
  {signed(neg, x) == Some{signed_word(neg, x)} : Maybe<&2, V.Int64>}
def signed_success(neg, x, h):
  checked_success(out_of_range(neg, x), signed_word(neg, x), h)

law signed_rejected:
  for +neg: Bool
  for +x: V.Int64
  for h: {out_of_range(neg, x) == True{} : Bool}
  {signed(neg, x) == None{} : Maybe<&2, V.Int64>}
def signed_rejected(neg, x, h):
  checked_rejected(out_of_range(neg, x), signed_word(neg, x), h)

law mul_success:
  for +a: V.Int64
  for +b: V.Int64
  for +m: V.Int64
  for calculation: {multiply_step(64n, magnitude(a), magnitude(b), V.Int64{0, 0}) == Some{m} : Maybe<&2, V.Int64>}
  for range: {out_of_range(Bool.xor(negative(a), negative(b)), m) == False{} : Bool}
  {mul(a, b) == Some{signed_word(Bool.xor(negative(a), negative(b)), m)} : Maybe<&2, V.Int64>}
def mul_success(a, b, m, calculation, range):
  %Equal.sym(Maybe<&2, V.Int64>, multiply_step(64n, magnitude(a), magnitude(b), V.Int64{0, 0}), Some{m}, calculation) :
    {sign_result(Bool.xor(negative(a), negative(b)), _) == Some{signed_word(Bool.xor(negative(a), negative(b)), m)} : Maybe<&2, V.Int64>}
  signed_success(Bool.xor(negative(a), negative(b)), m, range)

law division_by_zero:
  for a: V.Int64
  {divmod(a, V.Int64{0, 0}) == None{} : Maybe<&2, Division>}
def division_by_zero(a): {==}
