import Base
import ../../../contract/Theorems.bend as G
import ../../../contract/Semantics.bend as S
import ../Controls.bend as X
import ../WrongSteps.bend as Wrong
law false:
  G.Rejection(X.configuration(), X.seed(), X.request(), Wrong.accept, S.response_error(S.Certificate{}))
def false(): {==}
