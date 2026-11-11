import Base
import ../../../library/Value.bend as V
import ../../../library/Int64.bend as I
import ../../../library/Int64Multiplication.bend as P

# The magnitude of MIN is unsigned 2^63 and must survive multiplication by one.
law false:
  {I.mul(V.Int64{2147483648,0},V.Int64{0,1}) == None{} : Maybe<&2,V.Int64>}
def false(): {==}
