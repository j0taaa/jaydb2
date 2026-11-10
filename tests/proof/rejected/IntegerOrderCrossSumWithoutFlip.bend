import Base
import ../../../library/Int64WordIntegerOrder.bend as W

law false_negative_signed_cross_sum_equals_unsigned_word_order:
  {Nat.cmp(W.cross_left(1n,WCon{True{},WNil{}},WCon{False{},WNil{}}),W.cross_left(1n,WCon{False{},WNil{}},WCon{True{},WNil{}})) == Word.cmp(1n,WCon{True{},WNil{}},WCon{False{},WNil{}}) : Cmp}
def false_negative_signed_cross_sum_equals_unsigned_word_order(): {==}
