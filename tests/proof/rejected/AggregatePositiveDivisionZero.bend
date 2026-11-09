import Base
import ../../../library/Value.bend as V
import ../../../library/Int64DivisionSpec.bend as Division
import ../../../library/Int64PositiveDivision.bend as Positive

law false_negative_positive_division_can_drop_the_nonzero_condition:
  Positive.DivisionWitness<V.Int64{0,1},V.Int64{0,0}>
def false_negative_positive_division_can_drop_the_nonzero_condition():
  Positive.DivisionWitness{V.Int64{0,1},V.Int64{0,0},Division.Meaning{{==},{==},{==},{==},{==},{==}}}
