import Base
import ./Data.bend as D
import ./Requirements.bend as R
import ./Logic.bend as L
import ./Configuration.bend as C

def scenario(+id: String, seed: U32, drift: U32, volatility: U32) -> D.Row:
  D.Row{id, [D.Field{"drift", D.VInt{0, drift}}, D.Field{"id", D.VText{id}},
    D.Field{"seed", D.VInt{0, seed}}, D.Field{"volatility", D.VInt{0, volatility}}]}

def state() -> D.State:
  D.State{[D.Table{"results", Nil{}}, D.Table{"scenarios", [scenario("alice", 123456789, 0, 250),
    scenario("bob", 3735928559, 3, 700)]}], [
    D.Row{"alice", [D.Field{"credential", D.VText{"alice-token"}},
      D.Field{"id", D.VText{"alice"}}, D.Field{"kind", D.VText{"user"}}]},
    D.Row{"bob", [D.Field{"credential", D.VText{"bob-token"}},
      D.Field{"id", D.VText{"bob"}}, D.Field{"kind", D.VText{"user"}}]}]}

law initial_valid:
  R.Valid(C.config(), state())
def initial_valid():
  L.Both{{==}, L.Both{Unit{}, Unit{}}}
