import Base
import ../../../library/Value.bend as V
import ../../../contract/Logic.bend as L
import ../../../library/AggregateExtremaProofs.bend as E

# Zero is a valid lower bound here, but it is absent from the input.
law false_negative_minimum_needs_only_a_lower_bound:
  E.Extremum<True{},[V.Int64{0,1},V.Int64{0,2}],V.Int64{0,0}>
def false_negative_minimum_needs_only_a_lower_bound():
  E.Extremum{L.Left{{==}},E.Both{{==},E.Both{{==},Unit{}}}}
