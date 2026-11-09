# Signed overflow must reject instead of returning the wrapped maximum word.
import Base
import ../../../library/Int64.bend as I
import ../../../library/Value.bend as V

law false_minimum_minus_one_is_success:
  {I.sub(V.Int64{2147483648, 0}, V.Int64{0, 1}) == Some{V.Int64{2147483647, 4294967295}} : Maybe<&2, V.Int64>}
def false_minimum_minus_one_is_success():
  {==}
