import Base
import ./Data.bend as D
import ./Requirements.bend as R
import ./Logic.bend as L
import ./Configuration.bend as C

def state() -> D.State:
  D.State{Nil{}, [D.Row{"alice", [D.Field{"credential", D.VText{"demo"}},
    D.Field{"id", D.VText{"alice"}}, D.Field{"kind", D.VText{"user"}}]}]}

law initial_valid:
  R.Valid(C.config(), state())
def initial_valid():
  L.Both{{==}, Unit{}}
