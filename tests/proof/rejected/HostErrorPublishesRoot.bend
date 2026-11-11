import Base
import ../Controls.bend as State
import ../../../contract/Theorems.bend as T
import ../../../contract/Data.bend as D
import ../../../src/Control.bend as C

def root(result: C.Transition) -> D.State:
  match result:
    case C.ControlResult{next, last, reg, outcome}: next

law false:
  {root(C.host_error("HANDLE", State.seed(), Nil{}, C.ControlRegistry{Nil{}, Nil{}})) == State.changed() : D.State}
def false(): {==}
