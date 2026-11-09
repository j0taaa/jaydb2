import Base
import ../../../library/Value.bend as V
import ../../../library/Aggregate.bend as Aggregate
import ../../../library/Summary.bend as Summary

law false_negative_summary_rejects_empty_input:
  {Summary.compute([]) == None{} : Maybe<&2,Summary.Stats>}
def false_negative_summary_rejects_empty_input(): {==}
