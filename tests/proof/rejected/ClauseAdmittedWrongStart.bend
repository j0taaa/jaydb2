import Base
import ../../../contract/Theorems.bend as G
import ../../../contract/Logic.bend as L
import ../Controls.bend as X
import ../WrongSteps.bend as Wrong

# The Admitted clause of a step that starts X.program despite Reject.
law false:
  G.EntryCore(G.Admitted{}, Wrong.uncertified_begin(), X.configuration(), X.seed(), X.request(), X.reject)
def false():
  L.Both{{==}, (X.program(), L.Both{{==}, {==}})}
