# Deliberate false implementation: the success contract must reject it.
import Base
import ../../../library/Value.bend as V
import ../../../library/Int64.bend as I

def bad_add(a: V.Int64, b: V.Int64) -> Maybe<&2, V.Int64>:
  None{}

law bad_add_success:
  for +a: V.Int64
  for +b: V.Int64
  for h: {I.add_overflow(a, b) == False{} : Bool}
  {bad_add(a, b) == Some{I.wrapping_add(a, b)} : Maybe<&2, V.Int64>}
def bad_add_success(a, b, h):
  I.add_success_under_no_overflow(a, b, h)
