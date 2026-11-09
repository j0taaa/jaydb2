import Base
import ../../../library/Value.bend as V
import ../../../library/Aggregate.bend as Aggregate
import ../../../library/Summary.bend as Summary

law false_negative_average_can_reject_fitting_nonempty_input:
  {Aggregate.average([V.Int64{0,1},V.Int64{0,2}]) == None{} : Maybe<&2,V.Int64>}
def false_negative_average_can_reject_fitting_nonempty_input(): {==}
