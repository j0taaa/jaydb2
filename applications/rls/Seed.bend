import Base
import ./Data.bend as D
import ./Requirements.bend as R
import ./Logic.bend as L
import ./Configuration.bend as C
import ./Policy.bend as P

def user(+id: String, kind: String) -> D.Row:
  D.Row{id, [D.Field{"credential", D.VText{id ++ "-token"}},
    D.Field{"id", D.VText{id}}, D.Field{"kind", D.VText{kind}}]}

def state() -> D.State:
  D.State{[D.Table{"alice_dir", Nil{}}, D.Table{"bob_dir", Nil{}}, D.Table{"notes", Nil{}}],
    [user("admin", "admin"), user("alice", "user"), user("bob", "user")]}

law initial_valid:
  R.Valid(C.config(), state())
def initial_valid():
  L.Both{{==}, L.Both{P.Both{Unit{}, P.Both{Unit{}, P.Both{Unit{}, Unit{}}}},
    L.Both{L.Both{k => {==}, k => {==}}, Unit{}}}}
