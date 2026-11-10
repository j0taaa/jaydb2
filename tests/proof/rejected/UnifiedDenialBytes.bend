import Base
import ../../../contract/Theorems.bend as G
import ../../../contract/Semantics.bend as S
import ../../../contract/Logic.bend as L
import ../../../src/Resolve.bend as Resolve
import ../Controls.bend as X

# A denied prepared execution that answers with empty bytes.
law false:
  G.SelectedCore(G.Admitted{}, Resolve.Denied{S.Failure{}}, X.configuration(), X.seed(), X.reject)
def false(): (Nil{}, L.Both{{==}, L.Both{{==}, {==}}})
