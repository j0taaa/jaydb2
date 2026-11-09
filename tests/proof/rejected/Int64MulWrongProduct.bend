import Base
import ../../../library/Value.bend as V
import ../../../library/Int64UnsignedMultiply.bend as M

law false_wrong_product:
  M.UnsignedResult(Nat.mul(2n,3n),Some{V.Int64{0,7}})
def false_wrong_product(): {==}
