import Base
import ../../../library/Value.bend as V
import ../../../contract/Logic.bend as L
import ../../../library/AggregateExtremaProofs.bend as E

# Two belongs to the list but is not below its first element.
law false:
  E.Extremum<True{},[V.Int64{0,1},V.Int64{0,2}],V.Int64{0,2}>
def false():
  E.Extremum{L.Right{L.Left{{==}}},E.Both{{==},E.Both{{==},Unit{}}}}
