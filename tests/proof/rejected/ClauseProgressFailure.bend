import Base
import ../../../contract/Theorems.bend as G
import ../../../contract/Semantics.bend as S
import ../../../contract/Logic.bend as L
import ../../../src/Gate.bend as K
import ../Controls.bend as X
import ../WrongSteps.bend as Wrong

# Progress of a machine that already stopped with generic failure.
law false:
  G.EntryCore(G.Progressing{}, K.Started{X.context(), Wrong.failed_machine()}, X.configuration(), X.seed(), X.request(), X.reject)
def false():
  (0n, X.seed(), Nil{}, S.response_error(S.Failure{}), L.Both{{==},
    L.Both{(X.seed(), S.response_error(S.Failure{}), Wrong.failure_bytes(),
      L.Both{{==}, L.Both{{==}, L.Both{{==}, L.Both{X.seed_valid(), L.Both{{==}, L.Both{{==}, Unit{}}}}}}}),
      within => (X.seed(), S.response_error(S.Failure{}), Wrong.failure_bytes(), L.Both{{==}, Unit{}})}})
