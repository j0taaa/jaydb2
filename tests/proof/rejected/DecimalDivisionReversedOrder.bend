# The actual theorem cannot justify reversing the quotient comparison.
import Base
import ../../../proof/DecimalDivisionOrder.bend as O

law false_divide_ten_reverses_order:
  for +a: U32
  for +b: U32
  for less: {U32.is_le(a, b) == True{} : Bool}
  {U32.is_le(U32.div(b, 10), U32.div(a, 10)) == True{} : Bool}
def false_divide_ten_reverses_order(a, b, less):
  O.actual_u32_divide_ten_monotone(a, b, less)
