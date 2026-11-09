# Both 1<2 bounds and positivity are true, but 5=2*2+1 and 7=2*3+1
# describe different dividends. A shared dividend cannot be omitted.
import Base
import ../../../contract/Logic.bend as L
import ../../../library/Int64DivisionUnique.bend as E
law false_negative_distinct_dividends_have_the_same_quotient:
  L.E<{2n == 3n : Nat}, {1n == 1n : Nat}>
def false_negative_distinct_dividends_have_the_same_quotient():
  E.natural_euclidean_quotient_and_remainder_are_unique(5n, 2n, 2n, 1n, 3n, 1n,
    {==}, {==}, {==}, {==}, {==})
