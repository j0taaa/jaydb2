# Absolute magnitude preserves zero exactly; deriving nonzero division inputs.
import Base
import ./Value.bend as V
import ./Int64.bend as I
import ./Int64Proofs.bend as A
import ./Int64Flags.bend as G
import ./Int64RangeBits.bend as Bits
import ./Int64SignedMagnitude.bend as Signed
import ../proof/Foundations.bend as F

def zero_cases(zero: Bool, negated_zero: Bool, +x: V.Int64,
  actual: {I.zero(x) == zero : Bool}, negated: {I.zero(Bits.opposite(x)) == negated_zero : Bool}) ->
  {negated_zero == zero : Bool}:
  match zero negated_zero:
    case False{} False{}: {==}
    case True{} True{}: {==}
    case True{} False{}:
      F.absurd_boolean({False{} == True{} : Bool},
        Equal.trans(Bool, False{}, I.zero(Bits.opposite(x)), True{}, Equal.sym(Bool, I.zero(Bits.opposite(x)), False{}, negated),
          Equal.cong(V.Int64, Bool, word => I.zero(Bits.opposite(word)), x, V.Int64{0, 0}, G.zero_guard_is_sound(x, actual))))
    case False{} True{}:
      +same = Equal.trans(V.Int64, x, Bits.opposite(Bits.opposite(x)), V.Int64{0, 0},
        Equal.sym(V.Int64, Bits.opposite(Bits.opposite(x)), x, Signed.opposite_is_an_involution(x)),
        Equal.cong(V.Int64, V.Int64, Bits.opposite, Bits.opposite(x), V.Int64{0, 0}, G.zero_guard_is_sound(Bits.opposite(x), negated)))
      F.absurd_boolean({True{} == False{} : Bool},
        Equal.trans(Bool, False{}, I.zero(x), True{}, Equal.sym(Bool, I.zero(x), False{}, actual),
          Equal.cong(V.Int64, Bool, I.zero, x, V.Int64{0, 0}, same)))

law negation_preserves_exact_zero:
  for +x: V.Int64
  {I.zero(Bits.opposite(x)) == I.zero(x) : Bool}
def negation_preserves_exact_zero(x):
  zero_cases(I.zero(x), I.zero(Bits.opposite(x)), x, {==}, {==})

def absolute_zero_case(sign: Bool, +x: V.Int64, actual: {I.negative(x) == sign : Bool}) ->
  {I.zero(Bool.pick(V.Int64, sign, Bits.opposite(x), x)) == I.zero(x) : Bool}:
  match sign:
    case False{}: {==}
    case True{}: negation_preserves_exact_zero(x)

law actual_magnitude_preserves_exact_zero:
  for +x: V.Int64
  {I.zero(I.magnitude(x)) == I.zero(x) : Bool}
def actual_magnitude_preserves_exact_zero(x):
  absolute_zero_case(I.negative(x), x, {==})

def witness_is_strictly_positive(+x: V.Int64, positive: G.Positive<x>) ->
  {Nat.is_lt(0n, A.unsigned(x)) == True{} : Bool}:
  match positive:
    case G.Positive{+predecessor, exact}:
      Equal.cong(Nat, Bool, value => Nat.is_lt(0n, value), A.unsigned(x), 1n+predecessor, exact)

law nonzero_divisor_has_strictly_positive_magnitude:
  for +x: V.Int64
  for nonzero: {I.zero(x) == False{} : Bool}
  {Nat.is_lt(0n, A.unsigned(I.magnitude(x))) == True{} : Bool}
def nonzero_divisor_has_strictly_positive_magnitude(x, nonzero):
  witness_is_strictly_positive(I.magnitude(x),
    G.nonzero_has_positive_measure(I.magnitude(x),
      Equal.trans(Bool, I.zero(I.magnitude(x)), I.zero(x), False{}, actual_magnitude_preserves_exact_zero(x), nonzero)))
