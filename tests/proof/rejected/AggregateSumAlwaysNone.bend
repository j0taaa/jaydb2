import Base
import ../../../library/AggregateSumProofs.bend as S

law false:
  S.SumCorrect(Nil{},None{})
def false():
  S.checked_sum_is_right_fold_integer_addition(Nil{})
