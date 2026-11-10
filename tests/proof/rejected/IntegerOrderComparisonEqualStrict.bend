import Base
import ../../../library/Value.bend as V
import ../../../library/Int64.bend as I
import ../../../library/Aggregate.bend as Aggregate

law false_negative_equal_words_are_strictly_ordered:
  {I.lt(V.Int64{0,0},V.Int64{0,0}) == True{} : Bool}
def false_negative_equal_words_are_strictly_ordered(): {==}
