import Base
import ../Controls.bend as X
import ../../../contract/Theorems.bend as G

# A step starting X.program despite Reject must provide this Core clause.
law false:
  G.Admission(X.configuration(), X.request(), X.reject, X.context(), X.program())
def false(): {==}
