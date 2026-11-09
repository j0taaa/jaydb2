# Guarded word conversion with an exact tail fallback. The contract is unchanged;
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

# Keep runtime measurement scalar. This is mathematically the same low/high
# concatenation as the codec; only its proof reconstructs Word(64n).
def shift(k: Nat, value: Nat) -> Nat:
  match k:
    case 0n:
      value
    case 1n+p:
      Nat.double(shift(p, value))

def measure(number: B.Number64) -> Nat:
  match number:
    case B.Number64{high, low}:
      Nat.add(U32.to_nat(low), shift(32n, U32.to_nat(high)))

def candidate(+n: Nat) -> B.Number64:
  B.Number64{U32.from_nat(Nat.div(n, 1n+4294967295n)), U32.from_nat(n)}

def checked64(n: Nat, number: B.Number64, roundtrip: Bool) -> Maybe<&2, B.Number64>:
  match roundtrip:
    case False{}:
      nat64(n)
    case True{}:
      Some{number}

def nat64_wide(+n: Nat) -> Maybe<&2, B.Number64>:
  +number = candidate(n)
  checked64(n, number, Nat.is_eq(measure(number), n))

# The native compiler lowers these official Base conversions and comparison to
# primitive operations. A roundtrip guard proves this shortcut is applicable;
# larger naturals try a separately guarded64-word candidate before the exact
# all-domain tail fallback. No division-correctness assumption is needed.
def checked32(n: Nat, word: U32, roundtrip: Bool) -> Maybe<&2, B.Number64>:
  match roundtrip:
    case False{}:
      nat64_wide(n)
    case True{}:
      Some{B.Number64{0, word}}

def nat64_checked(+n: Nat) -> Maybe<&2, B.Number64>:
  +word = U32.from_nat(n)
  checked32(n, word, Nat.is_eq(U32.to_nat(word), n))

def length64(n: Nat) -> Maybe<&2, List<&2, U32>>:
  B.number64_bytes(nat64(n))
