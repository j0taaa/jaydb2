# An always-true comparator cannot inherit the actual structural soundness proof.
import Base
import ../../../contract/Data.bend as D
import ../../../library/ComparisonProofs.bend as P

def bad_equal(a: D.Value, b: D.Value) -> Bool:
  True{}

law bad_equal_sound:
  for +a: D.Value
  for +b: D.Value
  for +h: {bad_equal(a, b) == True{} : Bool}
  {a == b : D.Value}
def bad_equal_sound(a, b, h):
  P.equal_sound(a, b, h)
