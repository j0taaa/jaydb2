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
  {C.admitted(S.limits(State.configuration()), "controls", True{}, State.context(), "controls", X.handle(),
    C.apply(C.ControlRemove{"controls", X.handle()}, X.registered()), X.request()) == X.prepare_plan() : C.Plan}
def false(): {==}
