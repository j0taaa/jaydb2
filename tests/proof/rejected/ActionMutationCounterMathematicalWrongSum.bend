# Deliberately false FUNCTIONAL claim: reject at the proof body, not syntax.
import Base
import ../../../library/Value.bend as V
import ../../../library/Int64Proofs.bend as Math

law false:
  Math.IntegerSum(Math.integer(V.Int64{0,0}),Math.integer(V.Int64{0,1}),Math.integer(V.Int64{0,2}))
def false(): {==}
