import Base
import ../../../library/Value.bend as V
import ../../../library/Int64.bend as I
import ../../../library/Aggregate.bend as Aggregate

law false_negative_low_word_overrides_the_high_word:
  {I.lt(V.Int64{0,4294967295},V.Int64{1,0}) == False{} : Bool}
def false_negative_low_word_overrides_the_high_word(): {==}
