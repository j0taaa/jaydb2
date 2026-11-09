import Base
import ../../../library/Value.bend as V
import ../../../library/Aggregate.bend as Aggregate
import ../../../library/Summary.bend as Summary

law false_negative_summary_ignores_suffix_overflow:
  {Summary.compute([V.Int64{2147483648,0},V.Int64{2147483647,4294967295},V.Int64{0,1}]) == Some{Summary.Stats{V.Int64{0,3},V.Int64{0,0}}} : Maybe<&2,Summary.Stats>}
def false_negative_summary_ignores_suffix_overflow(): {==}
