import Base
import ../../../library/AggregateCountProofs.bend as C

law false:
  C.CountCorrect(Nil{},None{})
def false():
  C.checked_count_is_exact_representable_length(Nil{})
