import Base
import ../../../library/Value.bend as V
import ../../../library/Int64.bend as I
import ../../../library/Int64UnsignedMultiply.bend as M

# A single bit of fuel cannot establish the total theorem for multiplier two.
law false_insufficient_fuel:
  M.UnsignedResult(4n,I.multiply_step(1n,V.Int64{0,2},V.Int64{0,2},V.Int64{0,0}))
def false_insufficient_fuel(): {==}
