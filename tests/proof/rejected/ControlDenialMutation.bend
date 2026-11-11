import Base
import ../../../contract/Theorems.bend as T
import ../ControlInstances.bend as X
import ../Controls.bend as State
import ../../../contract/Data.bend as D
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/PreparedRegistry.bend as G
import ../../../contract/Semantics.bend as S
import ../../../src/Control.bend as C
import ../../../proof/ControlHistory.bend as H

law false:
  {T.next_registry(C.finish(C.ControlDenied{S.Authentication{}}, State.seed(), [1, 2], X.registry())) ==
    X.registered() : C.Registry}
def false(): {==}
