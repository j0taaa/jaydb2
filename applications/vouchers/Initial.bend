import Base
import ./Data.bend as D

def gate(owner: String) -> D.Row:
  D.Row{"permission", [D.Field{"enabled", D.VBool{True{}}},
    D.Field{"id", D.VText{"permission"}}, D.Field{"input", D.VAbsent{}},
    D.Field{"operation", D.VAbsent{}}, D.Field{"owner", D.VText{owner}},
    D.Field{"result", D.VAbsent{}}]}

def tables() -> List<&2, D.Table>:
  [D.Table{"alice", [gate("alice")]}, D.Table{"bob", [gate("bob")]}]

def origin(s: D.State) -> Data:
  D.State{ts, us} = s
  {ts == tables() : List<&2, D.Table>}
