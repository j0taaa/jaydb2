import Base
import ../../../library/Value.bend as V
import ../../../library/Aggregate.bend as A
import ../../../library/AggregateSumProofs.bend as S

# A representable final mathematical sum does not erase right-suffix overflow.
law false_negative_sum_ignores_suffix_overflow:
  {A.sum([V.Int64{2147483648,0},V.Int64{2147483647,4294967295},V.Int64{0,1}]) == Some{V.Int64{0,0}} : Maybe<&2,V.Int64>}
def false_negative_sum_ignores_suffix_overflow(): {==}
