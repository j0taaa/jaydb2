import Base
import ../../../library/Value.bend as V
import ../../../library/Aggregate.bend as Aggregate
import ../../../library/Summary.bend as Summary

law false_negative_summary_changes_total:
  {Summary.compute([V.Int64{0,3},V.Int64{0,5}]) == Some{Summary.Stats{V.Int64{0,2},V.Int64{0,9}}} : Maybe<&2,Summary.Stats>}
def false_negative_summary_changes_total(): {==}
