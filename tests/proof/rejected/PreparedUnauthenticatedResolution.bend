# Registered selection must authenticate against the current published root.
import Base
import ../Controls.bend as State
import ../ControlInstances.bend as X
import ../../../contract/Data.bend as D
import ../../../contract/Protocol.bend as P
import ../../../contract/Semantics.bend as S
import ../../../src/Resolve.bend as Resolve
import ../../../src/Control.bend as C

law false:
  {Resolve.select("controls", State.seed(), C.entries(X.registered()),
    Resolve.Registered{P.Request{"revoked-token", X.handle(), D.VAbsent{}, ""}}) ==
      Resolve.Selected{P.Request{"revoked-token", "refuse", D.VAbsent{}, "certificate"}} : Resolve.Selection}
def false(): {==}
