import Base
import ../../../contract/Theorems.bend as G
import ../../../src/Input.bend as Input
import ../Controls.bend as X

# An ordinary complete body never classifies as a transport error.
law false:
  G.DecodedCore(G.Safe{}, Input.ErrorTransport{}, X.configuration(), X.seed(), X.reject)
def false(): Unit{}
