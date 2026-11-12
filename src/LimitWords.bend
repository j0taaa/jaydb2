# A cached word carries its checked reference equality. Keep the selector
# generic so neither frontend normalizes a closed large Nat during rewriting.
import Base
import ../contract/Bytes.bend as B
import ../proof/Foundations.bend as F
import ../proof/LimitLiteral.bend as Literal

def select(number: B.Number64, matches: Bool, n: Nat) -> Maybe<&2, B.Number64>:
  match matches:
    case True{}: Some{number}
    case False{}: B.nat64(n)

# Expose the variable before comparing the closed ceiling. This keeps proof
# conversion from expanding the entire closed Nat in a stuck branch.
def matches(+n: Nat, +ceiling: Nat) -> Bool:
  match n:
    case 0n: Nat.is_eq(0n, ceiling)
    case 1n+p: Nat.is_eq(1n+p, ceiling)

def matches_exact(+n: Nat, +ceiling: Nat) ->
  {Nat.is_eq(n, ceiling) == matches(n, ceiling) : Bool}:
  match n:
    case 0n: {==}
    case 1n+p: {==}

def convert(+n: Nat, +ceiling: Nat, number: B.Number64,
  -represented: {B.nat64(ceiling) == Some{number} : Maybe<&2, B.Number64>}) -> Maybe<&2, B.Number64>:
  select(number, matches(n, ceiling), n)

# A compact Nat expression avoids Safe's deep Peano expansion of a literal.
# It is exactly 65,536 and is native constant multiplication at execution.
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

def select_exact(matches: Bool, +n: Nat, +ceiling: Nat, +number: B.Number64,
  represented: {B.nat64(ceiling) == Some{number} : Maybe<&2, B.Number64>},
  same: {Nat.is_eq(n, ceiling) == matches : Bool}) ->
  {select(number, matches, n) == B.nat64(n) : Maybe<&2, B.Number64>}:
  match matches:
    case False{}: {==}
    case True{}:
      Equal.sym(Maybe<&2, B.Number64>, B.nat64(n), Some{number},
        Literal.measured_equal(n, ceiling, number, natural_equal(n, ceiling, same), represented))

law convert_equals_reference:
  for +n: Nat
  for +ceiling: Nat
  for +number: B.Number64
  for represented: {B.nat64(ceiling) == Some{number} : Maybe<&2, B.Number64>}
  {convert(n, ceiling, number, represented) == B.nat64(n) : Maybe<&2, B.Number64>}
def convert_equals_reference(n, ceiling, number, represented):
  select_exact(matches(n, ceiling), n, ceiling, number, represented, matches_exact(n, ceiling))
