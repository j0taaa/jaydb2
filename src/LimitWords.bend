# Checked literal reuse without expanding a closed 65,536-node Nat in proofs.
import Base
import ../contract/Bytes.bend as B
import ../contract/Logic.bend as L
import ../proof/Foundations.bend as F
import ../proof/LimitLiteral.bend as Literal

def select(number: B.Number64, matches: Bool, n: Nat) -> Maybe<&2, B.Number64>:
  match matches:
    case True{}: Some{number}
    case False{}: B.nat64(n)

# Compare in bounded blocks. The guard only decrements native Nats; it never
# constructs the 65,536 intermediate u64 words of the reference conversion.
def trim(amount: Nat, n: Nat) -> Maybe<&2, Nat>:
  match amount n:
    case 0n n: Some{n}
    case 1n+k 0n: None{}
    case 1n+k 1n+p: trim(k, p)

def blocks_result(result: Maybe<&2, Nat>, next: Nat -> Bool) -> Bool:
  match result:
    case None{}: False{}
    case Some{rest}: next(rest)

def blocks(count: Nat, n: Nat) -> Bool:
  match count:
    case 0n: Nat.is_eq(n, 0n)
    case 1n+k: blocks_result(trim(256n, n), rest => blocks(k, rest))

def convert(+n: Nat) -> Maybe<&2, B.Number64>:
  select(B.Number64{0, 65536}, blocks(256n, n), n)

# Every Nat literal in the arithmetic witness is <=256. The product is exact.
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

def trim_sound(+amount: Nat, +n: Nat, +rest: Nat,
  same: {trim(amount, n) == Some{rest} : Maybe<&2, Nat>}) ->
  {n == Nat.add(amount, rest) : Nat}:
  match amount n:
    case 0n n: F.some_injective(Nat, n, rest, same)
    case 1n+k 0n:
      L.ex_false({0n == Nat.add(1n+k, rest) : Nat}, F.none_negative_some(Nat, rest, same))
    case 1n+k 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, p, Nat.add(k, rest), trim_sound(k, p, rest, same))

def after_block_sound(result: Maybe<&2, Nat>, +n: Nat, +k: Nat,
  same: {trim(256n, n) == result : Maybe<&2, Nat>},
  checked: {blocks_result(result, rest => blocks(k, rest)) == True{} : Bool},
  next: @rest: Nat -> {blocks(k, rest) == True{} : Bool} -> {rest == Nat.mul(k, 256n) : Nat}) ->
  {n == Nat.mul(1n+k, 256n) : Nat}:
  match result:
    case None{}:
      F.absurd_boolean({n == Nat.mul(1n+k, 256n) : Nat}, checked)
    case Some{+rest}:
      Equal.trans(Nat, n, Nat.add(256n, rest), Nat.mul(1n+k, 256n),
        trim_sound(256n, n, rest, same),
        Equal.trans(Nat, Nat.add(256n, rest), Nat.add(256n, Nat.mul(k, 256n)), Nat.mul(1n+k, 256n),
          Equal.cong(Nat, Nat, x => Nat.add(256n, x), rest, Nat.mul(k, 256n), next(rest, checked)),
          Equal.sym(Nat, Nat.mul(1n+k, 256n), Nat.add(256n, Nat.mul(k, 256n)), Literal.multiply_successor(k, 256n))))

def blocks_sound(+count: Nat, +n: Nat, checked: {blocks(count, n) == True{} : Bool}) ->
  {n == Nat.mul(count, 256n) : Nat}:
  match count:
    case 0n: natural_equal(n, 0n, checked)
    case 1n+k:
      after_block_sound(trim(256n, n), n, k, {==}, checked,
        rest => valid => blocks_sound(k, rest, valid))

def select_exact(matches: Bool, +n: Nat, +count: Nat, +number: B.Number64,
  represented: {B.nat64(Nat.mul(count, 256n)) == Some{number} : Maybe<&2, B.Number64>},
  same: {blocks(count, n) == matches : Bool}) ->
  {select(number, matches, n) == B.nat64(n) : Maybe<&2, B.Number64>}:
  match matches:
    case False{}: {==}
    case True{}:
      Equal.sym(Maybe<&2, B.Number64>, B.nat64(n), Some{number},
        Literal.measured_equal(n, Nat.mul(count, 256n), number, blocks_sound(count, n, same), represented))

law convert_equals_reference:
  for +n: Nat
  {convert(n) == B.nat64(n) : Maybe<&2, B.Number64>}
def convert_equals_reference(n):
  select_exact(blocks(256n, n), n, 256n, B.Number64{0, 65536}, common_literal_exact(), {==})
