import Base
import ../../../src/Core.bend as N
import ../../../contract/Semantics.bend as S
import ../../../contract/Data.bend as D
import ../Controls.bend as X
law false:
  {N.snapshot(N.start(X.program(), X.context(), D.VAbsent{}, X.changed())) ==
    N.snapshot(N.start(X.program(), X.context(), D.VAbsent{}, X.seed())) : S.Trace}
def false(): {==}
