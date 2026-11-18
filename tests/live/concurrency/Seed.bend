import Base
import ./Data.bend as D
import ./Requirements.bend as R
import ./Logic.bend as L
import ./Configuration.bend as C

def row(+id: String, value: U32) -> D.Row:
  D.Row{id, [D.Field{"id", D.VText{id}}, D.Field{"value", D.VInt{0, value}}]}

def state() -> D.State:
  D.State{[D.Table{"counters", [
    row("counter", 0),
    row("lane-a", 0), row("lane-b", 0), row("lane-c", 0), row("lane-d", 0),
    row("lane-e", 0), row("lane-f", 0), row("lane-g", 0), row("lane-h", 0),
    row("lane-i", 0), row("lane-j", 0), row("lane-k", 0), row("lane-l", 0),
    row("lane-m", 0), row("lane-n", 0), row("lane-o", 0), row("lane-p", 0),
    row("left", 100000), row("right", 0)]}],
    [D.Row{"alice", [D.Field{"credential", D.VText{"alice-token"}},
      D.Field{"id", D.VText{"alice"}}, D.Field{"kind", D.VText{"user"}}]}]}

law initial_valid:
  R.Valid(C.config(), state())
def initial_valid():
  L.Both{{==}, Unit{}}
