import Base
import ../../../library/Value.bend as V
import ../../../contract/Logic.bend as L
import ../../../library/AggregateExtremaProofs.bend as E

# Zero is a valid lower bound here, but it is absent from the input.
law false:
  E.Extremum<True{},[V.Int64{0,1},V.Int64{0,2}],V.Int64{0,0}>
def false():
  E.Extremum{L.Left{{==}},E.Both{{==},E.Both{{==},Unit{}}}}
