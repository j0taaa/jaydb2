# Tail-recursive length conversion. The contract conversion remains unchanged;
# proof/FastBytes proves equality for ALL naturals, including overflow to None.
import Base
import ../contract/Bytes.bend as B

def zero() -> Maybe<&2, B.Number64>:
  Some{B.Number64{0, 0}}

def advance(n: Nat, value: Maybe<&2, B.Number64>) -> Maybe<&2, B.Number64>:
  match n:
    case 0n:
      value
    case 1n+p:
      advance(p, B.increment64(value))

def nat64(n: Nat) -> Maybe<&2, B.Number64>:
  advance(n, zero())

# The native compiler lowers these official Base conversions and comparison to
# primitive operations. A roundtrip guard proves this shortcut is applicable;
# larger naturals retain the exact all-domain tail conversion above.
def checked32(n: Nat, word: U32, roundtrip: Bool) -> Maybe<&2, B.Number64>:
  match roundtrip:
    case False{}:
      nat64(n)
    case True{}:
      Some{B.Number64{0, word}}

def nat64_checked(+n: Nat) -> Maybe<&2, B.Number64>:
  +word = U32.from_nat(n)
  checked32(n, word, Nat.is_eq(U32.to_nat(word), n))

def length64(n: Nat) -> Maybe<&2, List<&2, U32>>:
  B.number64_bytes(nat64(n))
