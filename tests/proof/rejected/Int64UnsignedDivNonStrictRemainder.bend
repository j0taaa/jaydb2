import Base
import ../../../library/Value.bend as V
import ../../../library/Int64.bend as I
import ../../../library/Int64UnsignedDivision.bend as D
import ../../../contract/Logic.bend as L

# The arithmetic equality alone does not make a remainder of d valid.
law false:
  D.Euclidean(V.Int64{0,6},V.Int64{0,2},I.Division{V.Int64{0,2},V.Int64{0,2}})
def false():
  L.Both{{==},L.Both{{==},{==}}}
