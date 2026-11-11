import Base
import ../../../library/Value.bend as V
import ../../../contract/Logic.bend as L
import ../../../library/AggregateExtremaProofs.bend as E

# One belongs to the list but does not bound its second element above.
law false:
  E.Extremum<False{},[V.Int64{0,1},V.Int64{0,2}],V.Int64{0,1}>
def false():
  E.Extremum{L.Left{{==}},E.Both{{==},E.Both{{==},Unit{}}}}
