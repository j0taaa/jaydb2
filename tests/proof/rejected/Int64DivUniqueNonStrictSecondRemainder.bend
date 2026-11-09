# Reverse the same real decompositions: bounding just the first remainder
# cannot establish uniqueness. This catches accidental omission of small2.
import Base
import ../../../contract/Logic.bend as L
import ../../../library/Int64DivisionUnique.bend as E
law false_negative_only_first_remainder_requires_a_strict_bound:
  L.E<{1n == 0n : Nat}, {0n == 2n : Nat}>
def false_negative_only_first_remainder_requires_a_strict_bound():
  E.natural_euclidean_quotient_and_remainder_are_unique(2n, 2n, 1n, 0n, 0n, 2n,
    {==}, {==}, {==}, {==}, {==})
