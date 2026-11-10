import Base
import ../../../contract/Theorems.bend as G
import ../../../contract/Protocol.bend as P
import ../../../contract/Data.bend as D
import ../Controls.bend as X
law false:
  G.Identity(X.seed(), P.Request{"invalid", "refuse", D.VAbsent{}, "certificate"}, X.context())
def false(): {==}
