import Base
import ./Data.bend as D
import ./Requirements.bend as R
import ./Logic.bend as L
import ./Configuration.bend as C
import ./Policy.bend as Policy
import ./Initial.bend as Initial
import ./ReceiptLaws.bend as RL

def state() -> D.State:
  D.State{Initial.tables(), [
    D.Row{"alice", [D.Field{"credential", D.VText{"alice-token"}},
      D.Field{"id", D.VText{"alice"}}, D.Field{"kind", D.VText{"user"}}]},
    D.Row{"bob", [D.Field{"credential", D.VText{"bob-token"}},
      D.Field{"id", D.VText{"bob"}}, D.Field{"kind", D.VText{"user"}}]}]}

law initial_valid:
  R.Valid(C.config(), state())
def initial_valid():
  L.Both{{==}, L.Both{Policy.Both{Policy.Both{Policy.Both{{==}, {==}}, Unit{}},
    Policy.Both{Policy.Both{Policy.Both{{==}, {==}}, Unit{}}, Unit{}}}, L.Both{(state(), Nil{}, RL.Both{{==}, {==}}), Unit{}}}}
