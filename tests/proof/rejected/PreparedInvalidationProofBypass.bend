# A live handle and valid authentication cannot bypass empty-proof invalidation.
import Base
import ../Controls.bend as State
import ../ControlInstances.bend as X
import ../../../contract/Data.bend as D
import ../../../contract/Protocol.bend as P
import ../../../contract/Semantics.bend as S
import ../../../src/Dispatch.bend as Dispatch
import ../../../src/Input.bend as Input
import ../../../src/Control.bend as C

law false:
  {C.routed(S.limits(State.configuration()), "controls",
    Dispatch.Routed{5, Input.InputReady{State.seed(), P.Request{"token", X.handle(), D.VAbsent{}, "nonempty"}}},
    X.registered(), C.ControlUnaccepted{}, X.handle()) == X.invalidate_plan() : C.Plan}
def false(): {==}
