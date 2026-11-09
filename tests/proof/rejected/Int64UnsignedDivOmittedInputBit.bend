import Base
import ../../../library/Value.bend as V
import ../../../library/Int64.bend as I
import ../../../library/Int64UnsignedDivision.bend as D

law false_negative_omitted_dividend_bit:
  {I.divide_step(64n,V.Int64{0,7},V.Int64{0,3},V.Int64{0,0},V.Int64{0,0}) == I.Division{V.Int64{0,2},V.Int64{0,0}} : I.Division}
def false_negative_omitted_dividend_bit(): {==}
