# General arithmetic of actual codec sizes, including None on overflow.
# This entry does not assert complete Law 2 for the executable.
import Base
import ../contract/Bytes.bend as B
import ../src/Codec.bend as C
import ./CodecSumsBits.bend as S
import ./CodecSums64.bend as P

# TOTAL result: no representability premise is necessary.
# If an operand has already overflowed, the mathematical result is also None.
law sum_optional_nat64_exact:
  for +n: Nat
  for +m: Nat
  {C.sum_optional(B.nat64(n), B.nat64(m)) == B.nat64(Nat.add(n, m)) : Maybe<&2, B.Number64>}
def sum_optional_nat64_exact(n, m):
  P.represent_injective(C.sum_optional(B.nat64(n), B.nat64(m)), B.nat64(Nat.add(n, m)),
    Equal.trans(Maybe<&2, Word(64n)>,
      P.represent(C.sum_optional(B.nat64(n), B.nat64(m))),
      S.sum_optional(64n, P.represent(B.nat64(n)), P.represent(B.nat64(m))),
      P.represent(B.nat64(Nat.add(n, m))),
      P.sum_optional_represents_sum_binary(B.nat64(n), B.nat64(m)),
      Equal.trans(Maybe<&2, Word(64n)>,
        S.sum_optional(64n, P.represent(B.nat64(n)), P.represent(B.nat64(m))),
        S.natural(64n, Nat.add(n, m)), P.represent(B.nat64(Nat.add(n, m))),
        P.sum_naturals_represented(n, m),
        Equal.sym(Maybe<&2, Word(64n)>, P.represent(B.nat64(Nat.add(n, m))), S.natural(64n, Nat.add(n, m)), P.nat64_represents_natural_binary(Nat.add(n, m))))))

# Requested theorem about the actual function, for arbitrary counts and words.
law sum64_nat64_exact:
  for +n: Nat
  for +m: Nat
  for +x: B.Number64
  for +y: B.Number64
  for nx: {B.nat64(n) == Some{x} : Maybe<&2, B.Number64>}
  for my: {B.nat64(m) == Some{y} : Maybe<&2, B.Number64>}
  {C.sum64(x, y) == B.nat64(Nat.add(n, m)) : Maybe<&2, B.Number64>}
def sum64_nat64_exact(n, m, x, y, nx, my):
  %nx :
    {C.sum_optional(_, Some{y}) == B.nat64(Nat.add(n, m)) : Maybe<&2, B.Number64>}
  %my :
    {C.sum_optional(B.nat64(n), _) == B.nat64(Nat.add(n, m)) : Maybe<&2, B.Number64>}
  sum_optional_nat64_exact(n, m)

law nat_sum_zero_right:
  for +n: Nat
  {Nat.add(n, 0n) == n : Nat}
def nat_sum_zero_right(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, r => 1n+r, Nat.add(p, 0n), p, nat_sum_zero_right(p))

# The product need not fit: the result may be None.
law multiply_small_nat64_exact:
  for +k: Nat
  for +n: Nat
  for +x: B.Number64
  for +nx: {B.nat64(n) == Some{x} : Maybe<&2, B.Number64>}
  {C.multiply_small(k, x) == B.nat64(Nat.mul(k, n)) : Maybe<&2, B.Number64>}
def multiply_small_nat64_exact(k, n, x, nx):
  match k:
    case 0n:
      {==}
    case 1n:
      %Equal.sym(Nat, Nat.add(n, 0n), n, nat_sum_zero_right(n)) :
        {Some{x} == B.nat64(_) : Maybe<&2, B.Number64>}
      Equal.sym(Maybe<&2, B.Number64>, B.nat64(n), Some{x}, nx)
    case 2n+p:
      %nx :
        {C.sum_optional(_, C.multiply_small(1n+p, x)) == B.nat64(Nat.add(n, Nat.mul(1n+p, n))) : Maybe<&2, B.Number64>}
      %Equal.sym(Maybe<&2, B.Number64>, C.multiply_small(1n+p, x), B.nat64(Nat.mul(1n+p, n)), multiply_small_nat64_exact(1n+p, n, x, nx)) :
        {C.sum_optional(B.nat64(n), _) == B.nat64(Nat.add(n, Nat.mul(1n+p, n))) : Maybe<&2, B.Number64>}
      sum_optional_nat64_exact(n, Nat.mul(1n+p, n))
