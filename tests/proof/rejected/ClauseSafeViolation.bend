import Base
import ../../../contract/Theorems.bend as G
import ../../../contract/Data.bend as D
import ../../../contract/Logic.bend as L
import ../../../src/Core.bend as N
import ../Controls.bend as X

# The Safe clause, at the first prefix, of a started machine under a law that
# forbids every execution. Under X.configuration() the same proof is accepted.
law false:
  G.Safety(X.strict(), X.seed(), X.request(), X.context(),
    N.start(X.program(), X.context(), D.VAbsent{}, X.seed()), 0n)
def false():
  L.Both{L.Both{{==}, Unit{}}, L.Both{Unit{}, Unit{}}}
