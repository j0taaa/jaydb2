# With 0<=r<=d instead of r<d, 2=2*0+2=2*1+0 has distinct quotients.
# The exact equations and other strict bound pass; the dropped first strict
# bound is the precise rejected premise.
import Base
import ../../../contract/Logic.bend as L
import ../../../library/Int64DivisionUnique.bend as E
law false:
  L.E<{0n == 1n : Nat}, {2n == 0n : Nat}>
def false():
  E.natural_euclidean_quotient_and_remainder_are_unique(2n, 2n, 0n, 2n, 1n, 0n,
    {==}, {==}, {==}, {==}, {==})
