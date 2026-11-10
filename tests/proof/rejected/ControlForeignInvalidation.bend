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
  {C.invalidating(S.limits(State.configuration()), "other", True{}, State.context(), "other", X.registered(), X.handle()) ==
    X.invalidate_plan() : C.Plan}
def false(): {==}
