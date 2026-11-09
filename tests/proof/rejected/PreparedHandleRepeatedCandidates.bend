# Cardinality alone is insufficient if the candidate source repeats a value.
import Base
import ../../../proof/HandleCardinality.bend as F

law false_repeated_candidates_force_freshness:
  {F.search(["occupied", "occupied"], ["occupied"]) == Some{"fresh"} : Maybe<&2, String>}
def false_repeated_candidates_force_freshness():
  {==}
