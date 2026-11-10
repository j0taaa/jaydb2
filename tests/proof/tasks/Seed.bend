import Base
import ../../../contract/Data.bend as D
import ../../../contract/Requirements.bend as R
import ../../../contract/Logic.bend as L
import ./Configuration.bend as C
import ./Policy.bend as Policy

def state() -> D.State:
  D.State{[D.Table{"alice", Nil{}}, D.Table{"bob", Nil{}}], [
    D.Row{"alice", [D.Field{"credential", D.VText{"alice-token"}},
      D.Field{"id", D.VText{"alice"}}, D.Field{"kind", D.VText{"user"}}]},
    D.Row{"bob", [D.Field{"credential", D.VText{"bob-token"}},
      D.Field{"id", D.VText{"bob"}}, D.Field{"kind", D.VText{"user"}}]}]}

law initial_valid:
  R.Valid(C.config(), state())
def initial_valid():
  L.Both{{==}, L.Both{Policy.Both{Unit{}, Policy.Both{Unit{}, Unit{}}}, Unit{}}}
