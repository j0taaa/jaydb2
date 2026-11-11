import Base
import ../../../library/Value.bend as V
import ../../../library/Int64UnsignedMultiply.bend as M

law false:
  M.UnsignedResult(0n,None{})
def false():
  r => same => same
