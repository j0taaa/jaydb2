# Checked specialization of the common frozen byte ceiling. The fallback is
# the unchanged non-truncating reference conversion, including u64 overflow.
import Base
import ../contract/Bytes.bend as B
import ../proof/Foundations.bend as F
import ../proof/LimitLiteral.bend as Literal

def common() -> B.Number64:
  B.Number64{0, 65536}

def select(matches: Bool, n: Nat) -> Maybe<&2, B.Number64>:
  match matches:
    case True{}: Some{B.Number64{0, 65536}}
    case False{}: B.nat64(n)

def convert(+n: Nat) -> Maybe<&2, B.Number64>:
  select(Nat.is_eq(n, Nat.mul(256n, 256n)), n)

# The product is exactly 65,536, using small literals that also fit the
# default admission stack. Its closed u64 witness uses checked addition.
law common_literal_exact:
  {B.nat64(Nat.mul(256n, 256n)) == Some{B.Number64{0, 65536}} : Maybe<&2, B.Number64>}
def common_literal_exact():
  Literal.at_multiple_256()

def natural_equal(+a: Nat, +b: Nat, same: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n: {==}
    case 0n 1n+p: F.absurd_boolean({0n == 1n+p : Nat}, same)
    case 1n+p 0n: F.absurd_boolean({1n+p == 0n : Nat}, same)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, p, q, natural_equal(p, q, same))

def select_exact(matches: Bool, +n: Nat, same: {Nat.is_eq(n, Nat.mul(256n, 256n)) == matches : Bool}) ->
  {select(matches, n) == B.nat64(n) : Maybe<&2, B.Number64>}:
  match matches:
    case False{}: {==}
    case True{}:
      %Equal.sym(Nat, n, Nat.mul(256n, 256n), natural_equal(n, Nat.mul(256n, 256n), same)) :
        {Some{B.Number64{0, 65536}} == B.nat64(_) : Maybe<&2, B.Number64>}
      Equal.sym(Maybe<&2, B.Number64>, B.nat64(Nat.mul(256n, 256n)), Some{B.Number64{0, 65536}}, common_literal_exact())

law convert_equals_reference:
  for +n: Nat
  {convert(n) == B.nat64(n) : Maybe<&2, B.Number64>}
def convert_equals_reference(n):
  select_exact(Nat.is_eq(n, Nat.mul(256n, 256n)), n, {==})
