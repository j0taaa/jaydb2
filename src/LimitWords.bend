# Checked specialization of the common frozen byte ceiling. The fallback is
# the unchanged non-truncating reference conversion, including u64 overflow.
import Base
import ../contract/Bytes.bend as B
import ../proof/Foundations.bend as F
import ../proof/CodecRelaxArithmeticWord.bend as Measures
import ../proof/CodecSums64.bend as Bits


def select(common: Bool, n: Nat) -> Maybe<&2, B.Number64>:
  match common:
    case True{}: Some{B.Number64{0, 65536}}
    case False{}: B.nat64(n)


def convert(+n: Nat) -> Maybe<&2, B.Number64>:
  select(Nat.is_eq(n, 65536n), n)

# Keep the natural measure abstract during conversion checking, so neither
# checker needs to normalize the unary reference at the concrete ceiling.
def common_from_measure(+n: Nat,
  same: {n == Word.to_nat(64n, Bits.bits(B.Number64{0, 65536})) : Nat}) ->
  {B.nat64(n) == Some{B.Number64{0, 65536}} : Maybe<&2, B.Number64>}:
  %Equal.sym(Nat, n, Word.to_nat(64n, Bits.bits(B.Number64{0, 65536})), same) :
    {B.nat64(_) == Some{B.Number64{0, 65536}} : Maybe<&2, B.Number64>}
  Measures.nat64_measures_number(B.Number64{0, 65536})

law common_literal_exact:
  {B.nat64(65536n) == Some{B.Number64{0, 65536}} : Maybe<&2, B.Number64>}
def common_literal_exact():
  common_from_measure(65536n, {==})


def natural_equal(+a: Nat, +b: Nat, same: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n: {==}
    case 0n 1n+p: F.absurd_boolean({0n == 1n+p : Nat}, same)
    case 1n+p 0n: F.absurd_boolean({1n+p == 0n : Nat}, same)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, p, q, natural_equal(p, q, same))


def select_exact(common: Bool, +n: Nat, same: {Nat.is_eq(n, 65536n) == common : Bool}) ->
  {select(common, n) == B.nat64(n) : Maybe<&2, B.Number64>}:
  match common:
    case False{}: {==}
    case True{}:
      %Equal.sym(Nat, n, 65536n, natural_equal(n, 65536n, same)) :
        {Some{B.Number64{0, 65536}} == B.nat64(_) : Maybe<&2, B.Number64>}
      Equal.sym(Maybe<&2, B.Number64>, B.nat64(65536n), Some{B.Number64{0, 65536}}, common_literal_exact())

law convert_equals_reference:
  for +n: Nat
  {convert(n) == B.nat64(n) : Maybe<&2, B.Number64>}
def convert_equals_reference(n):
  select_exact(Nat.is_eq(n, 65536n), n, {==})
