import Base
import ../../../library/Value.bend as V
import ../../../library/Int64.bend as I
import ../../../library/Aggregate.bend as Aggregate

law false_negative_words_reverse_their_unsigned_order:
  {I.lt(V.Int64{4294967295,4294967294},V.Int64{4294967295,4294967295}) == False{} : Bool}
def false_negative_words_reverse_their_unsigned_order(): {==}
