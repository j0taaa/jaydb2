import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../src/Control.bend as C
import ../../../src/ControlBridge.bend as Wire
import ../../../src/Messages.bend as M

law false:
  for root: D.State
  for reg: C.Registry
  {Wire.output(C.host_error("PREPARED_INTEGRITY", root, Nil{}, reg)) == M.error(S.Certificate{}) : List<&2, U32>}
def false(root, reg): {==}
