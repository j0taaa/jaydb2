import Base
import ../../../library/AggregateCountProofs.bend as C

law false_negative_count_always_none:
  C.CountCorrect(Nil{},None{})
def false_negative_count_always_none():
  C.checked_count_is_exact_representable_length(Nil{})
