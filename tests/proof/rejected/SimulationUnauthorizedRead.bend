import Base
import ../../../contract/Data.bend as D
import ../SimulationPolicy.bend as C

# Exact installed application's access obligation: Alice cannot read Bob's scenario.
law false:
  C.Allowed(D.Context{"alice", "user"}, D.ReadCell{D.Application{"scenarios"}, "bob", "seed"})
def false():
  C.Both{{==}, {==}}
