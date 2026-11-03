import Base
import ./Data.bend as D
import ./Requirements.bend as R
import ./Logic.bend as L
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
