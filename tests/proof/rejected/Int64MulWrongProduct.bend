import Base
import ../../../library/Value.bend as V
import ../../../library/Int64UnsignedMultiply.bend as M

law false:
  M.UnsignedResult(Nat.mul(2n,3n),Some{V.Int64{0,7}})
def false(): {==}
