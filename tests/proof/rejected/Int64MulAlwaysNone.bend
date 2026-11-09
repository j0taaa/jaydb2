import Base
import ../../../library/Value.bend as V
import ../../../library/Int64UnsignedMultiply.bend as M

law false_always_none:
  M.UnsignedResult(0n,None{})
def false_always_none():
  r => same => same
