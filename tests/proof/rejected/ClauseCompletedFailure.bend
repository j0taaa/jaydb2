import Base
import ../../../contract/Theorems.bend as G
import ../../../contract/Semantics.bend as S
import ../../../contract/Logic.bend as L
import ../Controls.bend as X
import ../WrongSteps.bend as Wrong

# Completion of a final trace whose proposal is the generic failure status.
law false:
  G.Completion(X.configuration(), X.seed(), X.seed(), Nil{}, S.response_error(S.Failure{}))
def false():
  (X.seed(), S.response_error(S.Failure{}), Wrong.failure_bytes(),
    L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{X.seed_valid(), L.Both{{==}, L.Both{{==}, Unit{}}}}}}})
