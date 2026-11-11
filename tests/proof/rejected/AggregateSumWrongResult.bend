import Base
import ../../../library/Value.bend as V
import ../../../library/AggregateSumProofs.bend as S

law false:
  S.SumCorrect([V.Int64{0,1},V.Int64{0,2}],Some{V.Int64{0,4}})
def false():
  S.checked_sum_is_right_fold_integer_addition([V.Int64{0,1},V.Int64{0,2}])
