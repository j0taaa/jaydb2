# Original certificate bytes cannot restore authority after checked removal.
import Base
import ../Controls.bend as State
import ../ControlInstances.bend as X
import ../../../contract/Data.bend as D
import ../../../contract/Protocol.bend as P
import ../../../src/Resolve.bend as Resolve
import ../../../src/Control.bend as C

law false:
  {Resolve.select("controls", State.seed(),
    C.entries(C.apply(C.ControlRemove{"controls", X.handle()}, X.registered())),
    Resolve.Registered{X.invalidation()}) ==
      Resolve.Selected{P.Request{"token", "refuse", D.VAbsent{}, "certificate"}} : Resolve.Selection}
def false(): {==}
