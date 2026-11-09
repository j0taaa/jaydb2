# 0=0*0+0=0*1+0 does not determine a quotient. The zero-divisor
# counterexample is rejected at the actual positivity premise, before bounds.
import Base
import ../../../contract/Logic.bend as L
import ../../../library/Int64DivisionUnique.bend as E
law false_negative_zero_divisor_has_a_unique_quotient:
  L.E<{0n == 1n : Nat}, {0n == 0n : Nat}>
def false_negative_zero_divisor_has_a_unique_quotient():
  E.natural_euclidean_quotient_and_remainder_are_unique(0n, 0n, 0n, 0n, 1n, 0n,
    {==}, {==}, {==}, {==}, {==})
