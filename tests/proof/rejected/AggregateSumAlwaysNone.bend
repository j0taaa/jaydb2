import Base
import ../../../library/AggregateSumProofs.bend as S

law false_negative_sum_always_none:
  S.SumCorrect(Nil{},None{})
def false_negative_sum_always_none():
  S.checked_sum_is_right_fold_integer_addition(Nil{})
