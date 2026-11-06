# A vacuous strict order cannot replace the actual signed64 rank bridge.
import Base
import ../../../library/Value.bend as V
import ../../../library/ComparisonProofs.bend as P

def bad_lt(a: V.Int64,b: V.Int64) -> Bool:
  False{}

law bad_rank_bridge:
  for +a: V.Int64
  for +b: V.Int64
  {Cmp.is_lt(P.rank_order(a,b)) == bad_lt(a,b) : Bool}
def bad_rank_bridge(a,b):
  P.rank_matches_lt(a,b)
