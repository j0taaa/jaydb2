import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../src/Core.bend as N
import ../Controls.bend as X
law false:
  {N.traverse(0n, N.start(X.program(), X.context(), D.VAbsent{}, X.seed()), S.schema(X.configuration())) ==
    S.Final{X.seed(), Nil{}, S.Response{S.Refusal{}, D.VAbsent{}}} : S.Trace}
def false(): {==}
