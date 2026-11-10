import Base
import ../ControlInstances.bend as X
import ../Controls.bend as State
import ../../../contract/Data.bend as D
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/PreparedRegistry.bend as G
import ../../../contract/Semantics.bend as S
import ../../../src/Control.bend as C
import ../../../proof/ControlHistory.bend as H

law false:
  {H.next_registry(C.finish(C.receipt(S.Limits{1024n, 1024n, 64n}, "controls", State.context(),
    C.ControlAdd{X.entry()}, W.PreparedReceipt{X.handle()}), State.seed(), [1, 2], X.registry())) == X.registered() : C.Registry}
def false(): {==}
