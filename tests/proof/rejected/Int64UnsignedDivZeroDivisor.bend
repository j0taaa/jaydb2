import Base
import ../../../library/Value.bend as V
import ../../../library/Int64.bend as I
import ../../../library/Int64UnsignedDivision.bend as D
import ../../../contract/Logic.bend as L

# The equality 6=0*0+6 holds, but no remainder can be strictly below zero.
law false:
  D.Euclidean(V.Int64{0,6},V.Int64{0,0},I.Division{V.Int64{0,0},V.Int64{0,6}})
def false():
  L.Both{{==},L.Both{{==},{==}}}
