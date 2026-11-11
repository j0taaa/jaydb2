# Deliberately false input-content claim; must reject at the proof body.
import Base
import ../../../library/Index.bend as I
import ../../../library/Key.bend as K
import ../../../library/IndexKeyViewProofs.bend as Views
import ../../../library/ValueScalarProofs.bend as Pair



law false:
  Views.Absent(K.encode(["v"]),[I.unique(["v"],"stored")])
def false(): Pair.Both{{==},Unit{}}
