import Base
import ../../../library/Int64WordIntegerOrder.bend as W

law false:
  {Nat.cmp(W.cross_left(1n,WCon{True{},WNil{}},WCon{False{},WNil{}}),W.cross_left(1n,WCon{False{},WNil{}},WCon{True{},WNil{}})) == Word.cmp(1n,WCon{True{},WNil{}},WCon{False{},WNil{}}) : Cmp}
def false(): {==}
