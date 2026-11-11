import Base
import ../../../library/Value.bend as V
import ../../../library/Int64DivisionSpec.bend as Division
import ../../../library/Int64PositiveDivision.bend as Positive

law false:
  Positive.DivisionWitness<V.Int64{0,1},V.Int64{0,0}>
def false():
  Positive.DivisionWitness{V.Int64{0,1},V.Int64{0,0},Division.Meaning{{==},{==},{==},{==},{==},{==}}}
