import Base
import ../../../contract/Theorems.bend as G
import ../../../contract/Logic.bend as L
import ../../../src/Input.bend as Input
import ../Controls.bend as X

# A decoded request that arrives with a root different from the current one.
law false:
  G.DecodedCore(G.Safe{}, Input.InputReady{X.changed(), X.request()}, X.configuration(), X.seed(), X.reject)
def false(): L.Both{{==}, Unit{}}
