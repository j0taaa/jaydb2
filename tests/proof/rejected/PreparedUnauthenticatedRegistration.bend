# A universal admission tuple does not bypass current-root authentication.
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
    Dispatch.Routed{3, Input.InputReady{State.seed(), P.Request{"revoked-token", "refuse", D.VAbsent{}, "certificate"}}},
    X.registry(), X.admission(), X.handle()) == X.prepare_plan() : C.Plan}
def false(): {==}
