import Base
import ../../../library/Value.bend as V
import ../../../library/AggregateCountProofs.bend as C

law false:
  C.CountCorrect([V.Int64{0,7}],Some{V.Int64{0,2}})
def false():
  C.checked_count_is_exact_representable_length([V.Int64{0,7}])
