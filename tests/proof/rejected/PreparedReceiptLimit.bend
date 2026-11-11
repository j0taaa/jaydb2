# A receipt that exceeds the response limit cannot add its entry.
import Base
import ../Controls.bend as State
import ../ControlInstances.bend as X
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/Semantics.bend as S
import ../../../contract/Theorems.bend as T
import ../../../src/Control.bend as C

law false:
  {T.next_registry(C.finish(C.receipt(S.Limits{1024n, 1024n, 64n}, "controls", State.context(),
    C.ControlAdd{X.entry()}, W.PreparedReceipt{X.handle()}), State.seed(), [1, 2], X.registry())) ==
      X.registered() : C.Registry}
def false(): {==}
