# Cardinality alone is insufficient if the candidate source repeats a value.
import Base
import ../../../proof/HandleCardinality.bend as F

law false:
  {F.search(["occupied", "occupied"], ["occupied"]) == Some{"fresh"} : Maybe<&2, String>}
def false():
  {==}
