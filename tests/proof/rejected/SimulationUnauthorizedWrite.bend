import Base
import ../../../contract/Data.bend as D
import ../SimulationPolicy.bend as C

# Exact installed application's access obligation: Alice cannot write Bob.
law false:
  C.Allowed(D.Context{"alice", "user"}, D.DefineRow{D.Application{"results"}, "bob",
    [D.Field{"above", D.VInt{0, 0}}, D.Field{"id", D.VText{"bob"}},
      D.Field{"max", D.VInt{0, 1000000}}, D.Field{"paths", D.VInt{0, 1}},
      D.Field{"sum", D.VInt{0, 1000000}}]})
def false():
  C.Both{{==}, {==}}
