# A live entry cannot acquire provenance from an unaccepted admission token.
import Base
import ../Controls.bend as State
import ../ControlInstances.bend as X
import ../../../contract/Theorems.bend as T
import ../../../contract/Logic.bend as L
import ../../../src/Control.bend as C

law false:
  T.Tracked(State.configuration(), [X.entry()])
def false():
  L.Both{(C.ControlUnaccepted{}, L.Both{Unit{}, {==}}), Unit{}}
