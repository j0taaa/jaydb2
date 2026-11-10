import Base
import ../Controls.bend as X
import ../../../contract/Theorems.bend as G

# A step constructing Started{spoof(), ...} must provide this Core clause.
law false:
  G.Identity(X.seed(), X.request(), X.spoof())
def false(): {==}
